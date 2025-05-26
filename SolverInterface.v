Require Import SolverDefinitions.
Require Import SolverLemmas.

Definition Solver (cnf: CNF) := SolverDecreasing cnf (Vars cnf).

Theorem CorrectSat: forall (cnf: CNF) (m: Model), Solver cnf = Some m -> Models m cnf.
Proof.
  unfold Solver.
  intros cnf m Hsat.
  apply (CorrectSatDecreasing cnf m (Vars cnf)); auto.
Qed.

Theorem CorrectUnsat: forall (cnf: CNF), Solver cnf = None -> ~(exists m, Models m cnf).
Proof.
  unfold Solver.
  intros cnf Hunsat Hm.
  refine (CorrectUnsatDecreasing cnf (Vars cnf) _ Hunsat Hm); auto.
Qed.

Require Extraction ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "CoqSolver.hs" Solver.