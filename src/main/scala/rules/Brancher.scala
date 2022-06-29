// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.logger.SymbExLogger
import viper.silicon.state.State
import viper.silicon.state.terms.{Not, Term}
import viper.silicon.verifier.Verifier
import viper.silver.ast

trait BranchingRules extends SymbolicExecutionRules {
  def branch(s: State,
             condition: Term,
             conditionExp: Option[ast.Exp],
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fTrue: (State, Verifier) => VerificationResult,
             fFalse: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object brancher extends BranchingRules {
  def branch(s: State,
             condition: Term,
             conditionExp: Option[ast.Exp],
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fThen: (State, Verifier) => VerificationResult,
             fElse: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val negatedCondition = Not(condition)
    val negatedConditionExp = conditionExp.fold[Option[ast.Exp]](None)(c => Some(ast.Not(c)(pos = conditionExp.get.pos, info = conditionExp.get.info, ast.NoTrafos)))

    /* Skip path feasibility check if one of the following holds:
     *   (1) the branching is due to the short-circuiting evaluation of a conjunction
     *   (2) the branch condition contains a quantified variable
     */
    val skipPathFeasibilityCheck = (
         fromShortCircuitingAnd
      || (   s.quantifiedVariables.nonEmpty
          && s.quantifiedVariables.exists(condition.freeVariables.contains))
    )

    /* True if the then-branch is to be explored */
    val executeThenBranch = (
         skipPathFeasibilityCheck
      || !v.decider.check(negatedCondition, Verifier.config.checkTimeout()))

    /* False if the then-branch is to be explored */
    val executeElseBranch = (
         !executeThenBranch /* Assumes that ast least one branch is feasible */
      || skipPathFeasibilityCheck
      || !v.decider.check(condition, Verifier.config.checkTimeout()))

    // v.logger.info(s"Condition: ${condition}; Then: ${executeThenBranch}; Else: ${executeElseBranch}")

    val cnt = v.counter(this).next()

    val thenBranchComment = s"[then-branch: $cnt | $condition | ${if (executeThenBranch) "live" else "dead"}]"
    val elseBranchComment = s"[else-branch: $cnt | $negatedCondition | ${if (executeElseBranch) "live" else "dead"}]"

    v.decider.prover.comment(thenBranchComment)
    v.decider.prover.comment(elseBranchComment)

    val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(2, Some(condition))

    val elseBranchVerificationTask: Verifier => VerificationResult =
      if (executeElseBranch) {

        (v0: Verifier) => {
          SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
          SymbExLogger.currentLog().markReachable(uidBranchPoint)
          executionFlowController.locally(s, v0)((s1, v1) => {
            if (v.uniqueId != v1.uniqueId) {
              throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")
            }

            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            v1.decider.setCurrentBranchCondition(negatedCondition, negatedConditionExp)

            fElse(v1.stateConsolidator.consolidateIfRetrying(s1, v1), v1)
          })
        }
      } else {
        _ => Unreachable()
      }

    val elseBranch: VerificationResult =
      if (executeElseBranch) {
        elseBranchVerificationTask(v)
      } else {
        Unreachable()
      }

    val res = (if (executeThenBranch) {
      SymbExLogger.currentLog().markReachable(uidBranchPoint)
      executionFlowController.locally(s, v)((s1, v1) => {
        v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
        v1.decider.setCurrentBranchCondition(condition, conditionExp)

        fThen(v1.stateConsolidator.consolidateIfRetrying(s1, v1), v1)
      })
    } else {
      Unreachable()
    }) combine {
      elseBranch
    }
    SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
    res
  }
}
