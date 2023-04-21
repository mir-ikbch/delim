Set Implicit Arguments.

Inductive type : Type :=
| Nat : type
| Unit : type
| Func : type -> type -> type -> type -> type.

Notation "t / a --> s / b" := (Func t s a b) (at level 52, a at next level).
  
Section Var.
  Variable var : type -> Type.

  Inductive value : type -> Type :=
  | Var : forall t, var t -> value t
  | ConstN : nat -> value Nat
  | Tt : value Unit
  | Abs : forall dom ran a b, (var dom -> term ran a b) -> value (Func dom ran a b)
  with term : type -> type -> type -> Type :=
  | Val : forall t a, value t -> term t a a
  | Succ : forall a b, term Nat a b ->  term Nat a b
  | App : forall dom ran a b c d, term (Func dom ran a b) c d -> term dom b c -> term ran a d
  | Shift : forall t a b c x, (var (Func t a x x) -> term c c b) -> term t a b
  | Reset : forall c t a, term c c t -> term t a a.

End Var.

Arguments Var [var t] _.
Arguments Tt {var}.
Arguments ConstN [var] _.
Arguments Abs [var dom ran a b] _.
Arguments Val [var t a] _.
Arguments Shift [var t] _ [b c] _ _.


(** [x : Term t a b] means that the term [x] has type [t] and evaluation of it changes the answer type from [a] to [b]. *)
Definition Term t a b := forall var, term var t a b.
Definition Value t := forall var, value var t.


(** Target language of CPS translation *)

Inductive ttype : Type :=
| TNat : ttype
| TUnit : ttype
| TFunc : ttype -> ttype -> ttype.

Section TVar.
  Variable var : ttype -> Type.

  Inductive tterm : ttype -> Type :=
  | TVar : forall t, var t -> tterm t
  | TConstN : nat -> tterm TNat
  | TTt : tterm TUnit
  | TAbs : forall dom ran, (var dom -> tterm ran) -> tterm (TFunc dom ran)
  | TSucc : tterm TNat -> tterm TNat
  | TApp : forall dom ran, tterm (TFunc dom ran) -> tterm dom -> tterm ran
  | TLet : forall t1 t2, tterm t1 -> (var t1 -> tterm t2) -> tterm t2.
End TVar.

Arguments TVar [var t] _.
Arguments TConstN [var] _.
Arguments TAbs [var dom ran] _.

(** Translation of [tterm]s to Gallina terms. *)
Fixpoint ttypeDenote (t : ttype) : Type :=
  match t with
  | TNat => nat
  | TUnit => unit
  | TFunc t1 t2 => ttypeDenote t1 -> ttypeDenote t2
  end.

Fixpoint ttermDenote t (e : tterm ttypeDenote t) : ttypeDenote t :=
  match e with
  | TVar x => x
  | TConstN n => n
  | TTt _ => tt
  | TAbs f => fun x => ttermDenote (f x)
  | TSucc n => S (ttermDenote n)
  | TApp e1 e2 => ttermDenote e1 (ttermDenote e2)
  | TLet e1 e2 => ttermDenote (e2 (ttermDenote e1))
  end.


(** CPS translation *)
Fixpoint cps_type (t : type) : ttype :=
  match t with
  | Nat => TNat
  | Unit => TUnit
  | Func a b c d => TFunc (cps_type a) (TFunc (TFunc (cps_type b) (cps_type c)) (cps_type d))
  end.

Fixpoint cps_value var t (v : value (fun s => var (cps_type s)) t) : tterm var (cps_type t) :=
  match v with
  | Var x => TVar x
  | ConstN n => TConstN n
  | Tt => TTt _
  | Abs f => TAbs (fun x => cps_term _ (f x))
  end
with cps_term var t a b (e : term (fun s => var (cps_type s)) t a b) : tterm var (TFunc (TFunc (cps_type t) (cps_type a)) (cps_type b)) :=
       match e with
       | Val v => TAbs (fun k => TApp (TVar k) (cps_value _ v))
       | Succ e' => TAbs (fun k =>  TApp (cps_term _ e') (TAbs (fun n => TApp (TVar k) (TSucc (TVar n)))))
       | App e1 e2 => TAbs (fun k => TApp (cps_term _ e1) (TAbs (fun m => TApp (cps_term _ e2) (TAbs (fun n => TApp (TApp (TVar m) (TVar n)) (TVar k))))))
       | Shift _ _ f =>
           TAbs (fun k =>
                     TLet (TAbs (fun n => TAbs (fun k' => TApp (TVar k') (TApp (TVar k) (TVar n)))))
                          (fun k'' => TApp (cps_term _ (f k'')) (TAbs (fun m => TVar m))))
       | Reset _ e =>
           TAbs (fun k => TApp (TVar k) (TApp (cps_term _ e) (TAbs (fun m => TVar m))))
       end.



(** Examples *)

Example foo A B : Term _ _ _ :=
  fun (var : type -> Type) =>
    Shift A B (fun k => Val (Abs (fun (_ : var Unit) =>
                                 App (Val (Var k)) (Val (ConstN 0))))).
Check foo.
(*
 foo : forall A B : type, Term Nat A (Unit / B --> A / B)
*)

Example foo' A B var := cps_term var (foo A B _).

Eval compute in (ttermDenote (foo' Nat Unit _)).
(*
     = fun (x : nat -> nat) (_ : unit) (x1 : nat -> unit) => x1 (x 0)
*)

Example bar B C : Term _ _ _ :=
  fun (var : type -> Type) =>
    Reset C (Succ (foo _ B var)).
Check bar.
(*
  bar : forall B C : type, Term (Unit / B --> Nat / B) C C
 *)

Example bar' B C var := cps_term var (bar B C _).

Eval compute in (ttermDenote (bar' Unit Unit _)).
(*
     = fun x : (unit -> (nat -> unit) -> unit) -> unit => x (fun (_ : unit) (x1 : nat -> unit) => x1 1)
*)
