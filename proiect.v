(*MY PROGRAMMING LANGUAGE

Specificatii limbaj

-variabile;
-vectori
-atribuiri
-tipuri de date (natural.boolean,string,etc.)
-operatori peste tipurile natural si boolean
-instructiunile:if_then, if_then_else, while, for)

Netriviale
-metode pentru vectori(length(), sort(), push(), etc.)
-functii recursive
-simulare I/O
-expresii lambda
-clase+metode+obiecte
*)


Require Import List.
Import ListNotations.
Require Import Omega.
Delimit Scope string_scope with string.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.


Inductive tip_de_date :=
| eroare : tip_de_date
| nedef : tip_de_date
| Natural : nat -> tip_de_date
| Boolean : bool -> tip_de_date
| Str : string -> tip_de_date
| Vector : list nat -> tip_de_date.

Check Vector.

Coercion Boolean : bool >-> tip_de_date.
Coercion Natural : nat >-> tip_de_date.
Coercion Str : string >-> tip_de_date.


Definition eq_nedef (a b : tip_de_date) : bool :=
  match a,b with
  | nedef, nedef => true
  | _, _ => false
  end.

Definition eq_boolean (a b : tip_de_date) : bool :=
  match a, b with
  | false, false => true
  | true, true => true
  | _, _ => false
  end.

Inductive Var : Set :=
| newvar : string -> Var.

Scheme Equality for Var.

Coercion newvar : string >-> Var.

Definition eq_Var (v1 v2 : Var) : bool :=
  match v1,v2 with
  | newvar x, newvar y => if (eqb x y) 
                            then true
                            else false
  end. 


Inductive AExp :=
| avar : Var -> AExp
| anum : tip_de_date -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Coercion avar : Var >-> AExp.
Coercion anum : tip_de_date >-> AExp.

Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A -' B" := (aminus A B) (at level 50, left associativity).
Notation "A *' B" := (amul A B) (at level 40, left associativity).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (amod A B) (at level 40, left associativity).

Definition Env := Var -> tip_de_date.

Definition update (env : Env) (var : Var) (value : tip_de_date) : Env :=
  fun var' => if (eq_Var var' var)
              then value
              else (env var').

Definition env0 : Env := fun var => 0.

Compute env0 "variabila_test".

Definition plus (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Natural (n1 + n2)
  end.

Definition minus (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Natural (n1 - n2)
  end.

Definition mul (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Natural (n1 * n2)
  end.

Definition div (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => if (Nat.eqb n2 0)
                              then eroare
                              else Natural (Nat.div n1 n2)
  end.

Definition modulo (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => if (Nat.eqb n2 0)
                              then eroare
                              else Natural (Nat.modulo n1 n2)
  end.

Fixpoint aeval_fun (a : AExp) (env : Env) : tip_de_date :=
  match a with
  | anum (Natural n) => n
  | anum eroare => eroare
  | anum (Boolean b) => eroare
  | anum (Str s) => eroare
  | anum undef => eroare
  | avar var => env var
  | aplus a1 a2 => plus (aeval_fun a1 env) (aeval_fun a2 env)
  | aminus a1 a2 => minus (aeval_fun a1 env) (aeval_fun a2 env)
  | amul a1 a2 => mul (aeval_fun a1 env) (aeval_fun a2 env)
  | adiv a1 a2 => div (aeval_fun a1 env) (aeval_fun a2 env)
  | amod a1 a2 => modulo (aeval_fun a1 env) (aeval_fun a2 env)
  end.

Inductive BExp :=
| bbool : tip_de_date -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp
| blessequal: AExp -> AExp -> BExp
| bmoreequal : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| bequal : AExp -> AExp -> BExp.

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan A B) (at level 70).
Notation "A <=' B" := (blessequal A B) (at level 70).
Notation "A >=' B" := (bmoreequal A B) (at level 70).
Notation "! A" := (bnot A) (at level 75).
Notation "A /\' B" := (band A B) (at level 80).
Notation "A \/' B" := (bor A B) (at level 85).
Notation "A ==' B" := (bequal A B) (at level 70).

Definition less_than (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Nat.leb n1 n2 
  end.

Definition more_than (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Nat.leb n2 n1 
  end.

Definition equal (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 => Nat.eqb n1 n2 
  end.

Definition less_or_equal (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 =>if(Nat.eqb n1 n2)
                             then true
                             else if(Nat.leb n1 n2)
                                  then true
                                  else false
  end.

Definition more_or_equal (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Natural n1, Natural n2 =>if(Nat.eqb n1 n2)
                             then true
                             else if(Nat.leb n2 n1)
                                  then true
                                  else false
  end.

Definition _NOT_ (x : tip_de_date) : tip_de_date :=
  match x with
  | eroare => eroare
  | nedef => eroare
  | Natural n => eroare
  | Str s => eroare
  | Vector v => eroare
  | Boolean b => Boolean (negb b)
  end.

Definition _OR_ (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | eroare, _ => eroare
  | _, eroare => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Natural n, _ => eroare
  | _, Natural n => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Boolean b1, Boolean b2 => if (b1)
                              then Boolean b1
                              else Boolean b2
  end.

Definition _AND_ (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | eroare, _ => eroare
  | _, eroare => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Natural n, _ => eroare
  | _, Natural n => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Vector v, _ => eroare
  | _, Vector v => eroare
  | Boolean b1, Boolean b2 => if (b1)
                              then Boolean b2
                              else Boolean b1
  end.

Fixpoint beval_fun (b : BExp) (env : Env) : tip_de_date :=
  match b with
  | bbool b => b
  | bequal a1 a2 => equal (aeval_fun a1 env) (aeval_fun a2 env)
  | blessthan a1 a2 => less_than (aeval_fun a1 env) (aeval_fun a2 env)
  | bmorethan a1 a2 => more_than (aeval_fun a1 env) (aeval_fun a2 env)
  | blessequal a1 a2 => less_or_equal (aeval_fun a1 env) (aeval_fun a2 env)
  | bmoreequal a1 a2 => more_or_equal (aeval_fun a1 env) (aeval_fun a2 env)
  | bnot b' => _NOT_ (beval_fun b' env)
  | band b1 b2 => _AND_ (beval_fun b1 env) (beval_fun b2 env)
  | bor b1 b2 => _OR_ (beval_fun b1 env) (beval_fun b2 env)
  end.

Inductive Stmt :=
| declNat : tip_de_date -> Stmt
| declBool : tip_de_date -> Stmt
| declStr : tip_de_date -> Stmt
| declVect : tip_de_date -> Stmt
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Notation "-Nat A" := (declNat A) (at level 40).
Notation "-Bool A" := (declBool A) (at level 40).
Notation "-String A" := (declStr A) (at level 40).
Notation "-Vector A" := (declVect A) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "if( B )then{ S }" := (ifthen B S) (at level 45).
Notation "if( B )then{ S1 }else{ S2 }" := (ifthen B S1 S2) (at level 45).
Notation "While( B ){ S }" := (while B S) (at level 45).
Notation "for*( S1 ; B ; S2 ){ S3 }" := (For S1 B S2 S3) (at level 45).
 











