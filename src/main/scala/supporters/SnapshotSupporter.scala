// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.annotation.unused
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.state.{State, SymbolConverter}
import viper.silicon.state.terms.{Combine, First, Second, Sort, Term, Unit, sorts}
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier

trait SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean)

  def createSnapshotPair(sf: (Sort, Verifier) => Term,
                         v: Verifier)
                        : ((Sort, Verifier) => Term, (Sort, Verifier) => Term)
}

class DefaultSnapshotSupporter(symbolConverter: SymbolConverter) extends SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean) =
    optimalSnapshotSort(a, program, Nil)

  private def optimalSnapshotSort(a: ast.Exp, program: ast.Program, visited: Seq[String])
                                 : (Sort, Boolean) =

    a match {
      case _: ast.And if a.isPure =>
        (sorts.Snap, false)

      case _ if a.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(resacc, _) => resacc match {
        case fa: ast.FieldAccess =>
          (symbolConverter.toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName)) {
            program.findPredicate(pa.predicateName).body match {
              case None => (sorts.Snap, false)
              case Some(body) => optimalSnapshotSort(body, program, pa.predicateName +: visited)
            }
          } else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (sorts.Snap, false)

        case _: ast.MagicWand =>
          (sorts.Snap, false)
      }

      case ast.Implies(_, a1) =>
        /* a1 must be impure, otherwise the first case would have applied. */
        optimalSnapshotSort(a1, program, visited)

      case ast.And(a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(a1, a2, () => (sorts.Snap, false))

      case ast.CondExp(_, a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = optimalSnapshotSort(a1, program, visited)
          val (s2, isPure2) = optimalSnapshotSort(a2, program, visited)
          val s = if (s1 == s2) s1 else sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(a1, a2, () => findCommonSort())

      case QuantifiedPermissionAssertion(_, _, acc: ast.FieldAccessPredicate) =>
        (sorts.FieldValueFunction(symbolConverter.toSort(acc.loc.field.typ)), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(a1: ast.Exp,
                                             a2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean))
                                            : (Sort, Boolean) = {

    if (a1.isPure && a2.isPure) fIfBothPure()
    else (sorts.Snap, false)
  }

  def createSnapshotPair(sf: (Sort, Verifier) => Term,
                         v: Verifier)
                        : ((Sort, Verifier) => Term, (Sort, Verifier) => Term) = {

    val (snap0: Term, snap1: Term) = createSnapshotPair(sf(sorts.Snap, v), v)

    val sf0 = toSf(snap0)
    val sf1 = toSf(snap1)

    (sf0, sf1)
  }

  private def createSnapshotPair(snap: Term, v: Verifier): (Term, Term) = {

    assert(snap != Unit, "Unit snapshot cannot be decomposed")
    val snap0 = First(snap)
    val snap1 = Second(snap)

    v.decider.assume(snap === Combine(snap0, snap1))

    (snap0, snap1)
  }
}
