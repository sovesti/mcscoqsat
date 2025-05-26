Require Export Arith.
Require Export BinPos.
Require Export Bool.
Require Export List.
Require Export OrderedTypeEx.
Require Export MSets.

Local Open Scope positive.

Inductive Literal : Set :=
  | Var : positive -> Literal
  | Not : positive -> Literal.

Definition LitToBool (l: Literal) :=
  match l with
  | Var _ => true
  | Not _ => false
  end.

Inductive Clause : Set :=
  | Bottom
  | Or : Clause -> Literal -> Clause.

Inductive CNF : Set :=
  | Top
  | And : CNF -> Clause -> CNF.

Definition Max (φ ψ : bool) : bool :=
  match φ, ψ with
  | false, false => false
  | _, _ => true
  end.

Definition Min (φ ψ : bool) : bool :=
  match φ, ψ with
  | true, true => true
  | _, _ => false
  end.

Definition flip_bool (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Module VarSet := Make Positive_as_OT.

Definition Model := VarSet.t.

Definition EvalLiteral (m: Model) (l : Literal) : bool :=
  match l with
  | Var p => VarSet.mem p m
  | Not p => flip_bool (VarSet.mem p m)
  end.

Fixpoint EvalClause (M: Model) (c : Clause) : bool :=
  match c with
  | Bottom => false
  | Or c' l => Max (EvalClause M c') (EvalLiteral M l)
  end.

Fixpoint EvalCnf (M: Model) (cnf : CNF) : bool :=
  match cnf with
  | Top => true
  | And cnf' clause => Min (EvalCnf M cnf') (EvalClause M clause)
  end.

Definition Models M φ := (EvalCnf M φ) = true.

Definition LitToVar (l: Literal) : positive :=
  match l with
  | Var v => v
  | Not v => v
  end.

Fixpoint VarsClause (c: Clause) : VarSet.t :=
  match c with
  | Bottom => VarSet.empty
  | Or c' l => VarSet.add (LitToVar l) (VarsClause c')
  end.

Fixpoint VarsCnf (cnf: CNF) : VarSet.t :=
  match cnf with
  | Top => VarSet.empty
  | And cnf' c => VarSet.union (VarsClause c) (VarsCnf cnf')
  end.

Definition AnyVar (cnf: CNF) : option positive := VarSet.choose (VarsCnf cnf).

Definition SameVarLiterals (l: Literal) (l': Literal) : bool := LitToVar l =? LitToVar l'.

Definition SameLiterals (l: Literal) (l': Literal) : bool :=
  match l, l' with
  | Var v, Var v' => v =? v'
  | Not v, Not v' => v =? v'
  | _, _ => false
  end.

Definition OppositeLiterals (l: Literal) (l': Literal) : bool :=
  match l, l' with
  | Var v, Not v' => v =? v'
  | Not v, Var v' => v =? v'
  | _, _ => false
  end.

Fixpoint ClauseContains (c: Clause) (l: Literal) : bool :=
  match c, l with
  | Bottom, _ => false
  | Or c' any, l => if SameLiterals any l then true else ClauseContains c' l
  end.

Fixpoint ContainsBottom (cnf: CNF) : bool :=
  match cnf with
  | Top => false
  | And cnf' Bottom => true
  | And cnf' _ => ContainsBottom cnf'
  end.

Fixpoint PropagateClause (c: Clause) (l: Literal) : Clause :=
  match c with
  | Bottom => Bottom
  | Or c' l' => if OppositeLiterals l l' 
                  then PropagateClause c' l
                  else Or (PropagateClause c' l) l'
  end.

Fixpoint RemoveSatisfied (cnf: CNF) (l: Literal) : CNF :=
  match cnf with
  | Top => Top
  | And cnf' c => if ClauseContains c l 
                    then RemoveSatisfied cnf' l
                    else And (RemoveSatisfied cnf' l) c
  end.

Fixpoint PropagateCnf (cnf: CNF) (l: Literal) : CNF :=
  match cnf with
  | Top => Top
  | And cnf' c => And (PropagateCnf cnf' l) (PropagateClause c l)
  end.

Definition CleanCnf (cnf: CNF) (l: Literal) : CNF :=
  PropagateCnf (RemoveSatisfied cnf l) l.
  
Fixpoint FindPure (cnf: CNF): option Literal :=
  match cnf with
  | Top => None
  | And cnf' c => match c with
                  | Or Bottom l => Some l
                  | _ => FindPure cnf'
                  end
  end.

Definition Vars := fun cnf: CNF => VarSet.cardinal (VarsCnf cnf).

Definition ExpandModel (m: Model) (l: Literal) : Model :=
  match l with
  | Var v => VarSet.add v m
  | Not v => VarSet.remove v m
  end.

Definition ExpandResult (r: option Model) (l: Literal) := 
  match r with
  | Some m => Some (ExpandModel m l)
  | None => None
  end.

Fixpoint SolverDecreasing (cnf: CNF) (steps: nat): option Model := 
  if ContainsBottom cnf then None else 
    match steps with
    | O => Some VarSet.empty
    | S vs => 
      match FindPure cnf with
        | Some l => ExpandResult (SolverDecreasing (CleanCnf cnf l) vs) l
        | None => 
          match AnyVar cnf with
            | Some v => match SolverDecreasing (CleanCnf cnf (Var v)) vs with
                          | Some m => ExpandResult (Some m) (Var v)
                          | None => ExpandResult (SolverDecreasing (CleanCnf cnf (Not v)) vs) (Not v)
                        end
            | None => Some VarSet.empty
          end
      end
    end.

Definition Solver (cnf: CNF) := SolverDecreasing cnf (Vars cnf).

Local Close Scope positive.