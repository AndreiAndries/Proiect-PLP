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
| Str : string -> tip_de_date.

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

Notation "A +' B" := (aplus A B) (at level 49, left associativity).
Notation "A -' B" := (aminus A B) (at level 49, left associativity).
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

Inductive SExp :=
| sstring : tip_de_date -> SExp 
| sstrcmp : SExp -> SExp -> SExp
| sconcat : SExp -> SExp -> SExp
| slength : SExp -> SExp.

Coercion sstring : tip_de_date >-> SExp.

Notation "strcmp( A , B )" := (sstrcmp A B) (at level 70).
Notation "concat( A , B )" := (sconcat A B) (at level 50). 
Notation "length( A )" := (slength A) (at level 50). 

Definition _CMP_ (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Natural n, _ => eroare
  | _, Natural n => eroare
  | Str s1, Str s2 => String.eqb s1 s2 
  end.

Definition _CONCAT_ (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Natural n, _ => eroare
  | _, Natural n => eroare
  | Str s1, Str s2 => String.append s1 s2 
  end.

Definition _LENGTH_ (x : tip_de_date) : tip_de_date :=
  match x with
  | eroare => eroare
  | nedef => eroare
  | Natural n => eroare
  | Boolean b => eroare
  | Str s => String.length s
  end.

Fixpoint seval_fun (s : SExp) (env : Env) : tip_de_date :=
  match s with
  | sstring s => s
  | sstrcmp s1 s2 => _CMP_ (seval_fun s1 env) (seval_fun s2 env)
  | sconcat s1 s2 => _CONCAT_ (seval_fun s1 env) (seval_fun s2 env)
  | slength s => _LENGTH_ (seval_fun s env)
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
| bequal : AExp -> AExp -> BExp
| bnequal : AExp -> AExp -> BExp.

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan A B) (at level 70).
Notation "A <=' B" := (blessequal A B) (at level 70).
Notation "A >=' B" := (bmoreequal A B) (at level 70).
Notation "! A" := (bnot A) (at level 75).
Notation "A /\' B" := (band A B) (at level 80).
Notation "A \/' B" := (bor A B) (at level 85).
Notation "A ==' B" := (bequal A B) (at level 70).
Notation "A !=' B" := (bnequal A B) (at level 70).

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
  | Natural n1, Natural n2 => Nat.eqb n1 n2 
  end.

Definition not_equal (x1 x2 : tip_de_date) : tip_de_date :=
  match x1, x2 with
  | _, eroare => eroare
  | eroare, _ => eroare
  | nedef, _ => eroare
  | _, nedef => eroare
  | Boolean b, _ => eroare
  | _, Boolean b => eroare
  | Str s, _ => eroare
  | _, Str s => eroare
  | Natural n1, Natural n2 => if(Nat.eqb n1 n2)
                              then false
                              else true 
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
  | Boolean b1, Boolean b2 => if (b1)
                              then Boolean b2
                              else Boolean b1
  end.


Fixpoint beval_fun (b : BExp) (env : Env) : tip_de_date :=
  match b with
  | bbool b => b
  | bequal a1 a2 => equal (aeval_fun a1 env) (aeval_fun a2 env)
  | bnequal a1 a2 => not_equal (aeval_fun a1 env) (aeval_fun a2 env)
  | blessthan a1 a2 => less_than (aeval_fun a1 env) (aeval_fun a2 env)
  | bmorethan a1 a2 => more_than (aeval_fun a1 env) (aeval_fun a2 env)
  | blessequal a1 a2 => less_or_equal (aeval_fun a1 env) (aeval_fun a2 env)
  | bmoreequal a1 a2 => more_or_equal (aeval_fun a1 env) (aeval_fun a2 env)
  | bnot b' => _NOT_ (beval_fun b' env)
  | band b1 b2 => _AND_ (beval_fun b1 env) (beval_fun b2 env)
  | bor b1 b2 => _OR_ (beval_fun b1 env) (beval_fun b2 env)
  end.

Definition Vector := list nat.

Definition Length (v : Vector) : nat := List.length v.

Definition Pushfront (v : Vector) (n : nat): Vector := n :: v.  

Definition Pop (v : Vector) : Vector := List.removelast v.

Definition index (v : Vector) (n : nat) : nat := List.nth n v 0.

Notation "VLength( A )" := (Length A) (at level 50). 
Notation "Pushfront( V , X )" := (Pushfront V X) (at level 50).
Notation "Pop( V )" := (Pop V) (at level 50).
Notation " V [' I ]'" := (index V I) (at level 40).

Compute VLength( [10;20;30] ).
Definition L1 := Pushfront( [10;20;30] , 40 ).
Compute L1.
Compute L1['2]'.
Compute (List.last L1).
Definition L2 := Pop( L1 ).
Definition L0 := Pop (Pop( Pop( Pop( L1) ) ) ).
Compute L2.
Compute L0.

Inductive Stmt :=
| declNat : tip_de_date -> Stmt
| declBool : tip_de_date -> Stmt
| declStr : tip_de_date -> Stmt
| declVect : Vector -> Stmt
| varib : Var -> Stmt
| declObiect : Var -> Var -> Stmt
| obfunc: Var -> Var -> Stmt
| vctlng: Vector -> Stmt
| obfuncpar: Var -> Var -> Stmt -> Stmt
| obtip : Var -> Var -> Stmt
| assignment : Var -> AExp -> Stmt
| sassignment : Var -> SExp -> Stmt
| assignment1 : Var -> Stmt -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| Struct : Var -> Stmt -> Var -> Stmt
| CLASS : Var -> Stmt -> Stmt -> Stmt
| function : Var -> Stmt -> Stmt -> Stmt
| function_antet : Var -> Stmt -> Stmt.


Notation "-Nat A" := (declNat A) (at level 40).
Notation "-Bool A" := (declBool A) (at level 40).
Notation "-String A" := (declStr A) (at level 40).
Notation "-Vector A" := (declVect A) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "X ::=' A" := (assignment1 X A) (at level 50).
Notation "cpy( X , A )" := (sassignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "if( B ){ S }" := (ifthen B S) (at level 45).
Notation "if( B ){ S1 }ELSE{ S2 }" := (ifthenelse B S1 S2) (at level 45).
Notation "While( B ){ S }" := (while B S) (at level 45).
Notation "for*( S1 ; B ; S2 ){ S3 }" := (For S1 B S2 S3) (at level 45).
Notation "vect_length( N )" := (vctlng N) (at level 49). 
Notation "struct( NAME ){ S } VAR " := (Struct NAME S VAR) (at level 40).
Notation "CLASS( NAME ){ PRIVATE: S1 PUBLIC: S2 } " := (CLASS NAME S1 S2) (at level 40).
Notation " V ( S1 ) " := (function_antet V S1) ( at level 50).
Notation " function N ( S1 ){ S2 } ":= (function N S1 S2) (at level 44).
Notation " X ->' Y ":= (obtip X Y) (at level 40).
Notation " X ->' Y ()":= (obfunc X Y) (at level 50).
Notation " X ->' Y ( Z )":=(obfuncpar X Y Z) (at level 50). 

Check -Nat "x".
Check -Bool "ok".
Compute -String "newstr".
Compute -Vector L1.
Compute "x" ::= 15 +' 16.
Compute cpy( "x" , "Ana are mere").
Compute "x"::= 10 *' 2 ;; cpy( "a" , "test") ;; -Nat "a".
Compute if( "a" <=' 10 ){
  "a"::=10 ;;
  -Bool "ok1" ;; -Bool "ok2" ;; -Vector L0 ;; 
  cpy( "x" , "Ana are mere")
}.
Compute if( "a" <=' 10 ){
  "a"::=10 ;;
  -Bool "ok1" ;; -Bool "ok2" ;; -Vector L1 ;; 
  cpy( "x" , "Ana are mere")
}ELSE{
  "a"::= "a" /' 2 ;; 
  -Vector L0  
}.
Compute While( "a" !=' 10 \/' "a"!=' 100){
  if( "a" >=' 50 ){
    if( "a" <' 100){
      "a"::="a" +' 1
    }ELSE{
      "a"::="a" -' 1
    }
  }ELSE{
    if("a" >' 10){
      "a"::="a" -' 1
    }ELSE{
      "a"::="a" +' 1
    }
  }
}. 

Compute
-Nat "par" ;; -Nat "impar" ;;
"par"::= 0 ;; "impar"::= 0 ;;
for*("i" ::= 0 ; "i" <=' 10 ; "i"::= "i" +' 1){
  if( "a" %' 2 ==' 0){
  "par"::="par" +' 1
  }ELSE{
  "impar"::="impar" +' 1
  } ;;
  -String "str"
}.

Compute
struct("structura_noua"){
  -Nat "natural" ;;
  -String "string" ;;
  -Bool "bool" ;;
  -Vector []
}"ob_struct" ;;
-Nat "par" ;; -Nat "impar" ;;
"par"::= 0 ;; "impar"::= 0 ;;
for*("i" ::= 0 ; "i" <=' 10 ; "i"::= "i" +' 1){
  if( "a" %' 2 ==' 0){
  "par"::="par" +' 1
  }ELSE{
  "impar"::="impar" +' 1
  }
}.








