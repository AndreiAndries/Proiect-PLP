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

Inductive Vectfun :=
| vlength : Vector -> Vectfun
| vpushfr : Vector -> nat -> Vectfun
| vpushfrvar : Vector -> Var -> Vectfun
| vpush : Vector -> nat -> Vectfun
| vpushvar : Vector -> Var -> Vectfun
| vpop : Vector -> Vectfun
| vindex : Vector -> nat -> Vectfun
| vreverse : Vector -> Vectfun.

Definition _Length_ (v : Vector) : nat := List.length v.

Definition _Pushfront_ (v : Vector) (n : nat): Vector := n :: v.  

Definition _Pop_ (v : Vector) : Vector := List.removelast v.

Definition _index_ (v : Vector) (n : nat) : nat := List.nth n v 0.

Definition _reverse_ (v : Vector) : Vector := List.rev v.

Definition _push_ (v : Vector) (n : nat) : Vector := List.rev ( n :: List.rev v).

Notation "VLength( A )" := (vlength A) (at level 50). 
Notation "Pushfront( V , X )" := (vpushfr V X) (at level 50).
Notation "Pop( V )" := (vpop V) (at level 50).
Notation " V [' I ']" := (vindex V I) (at level 40).
Notation "Push( V , A )" := (vpush V A) (at level 50).
Notation "Reverse( V )" := (vreverse V) (at level 50).
Notation "PushVar( V , A )" := (vpushvar V A) (at level 50).
Notation "PushfrontVar( V , X )" := (vpushfrvar V X) (at level 50).

Notation "VLength1( A )" := (_Length_ A) (at level 50). 
Notation "Pushfront1( V , X )" := (_Pushfront_ V X) (at level 50).
Notation "Pop1( V )" := (_Pop_ V) (at level 50).
Notation " V [' I ]'" := (_index_ V I) (at level 40).
Notation "Push1( V , A )" := (_push_ V A) (at level 50).
Notation "Reverse1( V )" := (_reverse_ V) (at level 50).

Compute VLength1( [10;20;30] ).
Definition L1 := Pushfront1( [10;20;30] , 40 ).
Compute L1.
Compute L1['2]'.
Compute (List.last L1).
Definition L2 := Pop1( L1 ).
Definition L0 := Pop1( Pop1( Pop1( Pop1( L1) ) ) ).
Compute L2.
Compute L0.
Compute L2.
Compute Push1(Push1(L2,5),11).
Compute Reverse1(L2).

Inductive Stmt :=
| declNat : tip_de_date -> Stmt
| declBool : tip_de_date -> Stmt
| declStr : tip_de_date -> Stmt
| declVect : Vector -> Stmt
| returnNat : tip_de_date -> Stmt
| returnBool : tip_de_date -> Stmt
| returnStr : tip_de_date -> Stmt
| returnVect : Vector -> Stmt
| scan : tip_de_date -> Stmt
| print : tip_de_date -> Stmt
| varib : tip_de_date -> Stmt
| declObiect : Var -> Var -> Stmt
| obfunc: Var -> Var -> Stmt
| vfun : Vectfun -> Stmt
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
| function1 : Var -> Stmt -> Stmt
| constructor : Var -> Stmt -> Stmt
| constructor1 : Var -> Stmt
| destructor : Var -> Stmt
| function_antet : Var -> Stmt -> Stmt
| simple_lambda : Var -> Stmt -> Stmt -> Stmt
| passbyvalue_lambda : Var -> Stmt -> Stmt -> Stmt
| passvars_lambda : Var -> Stmt -> Stmt -> Stmt -> Stmt.

Coercion vfun : Vectfun >-> Stmt.
Coercion varib : tip_de_date >-> Stmt.
Notation "-Nat A" := (declNat A) (at level 40).
Notation "-Bool A" := (declBool A) (at level 40).
Notation "-String A" := (declStr A) (at level 40).
Notation "-Vector A" := (declVect A) (at level 40).
Notation "-RetNat A" := (returnNat A) (at level 40).
Notation "-RetBool A" := (returnBool A) (at level 40).
Notation "scan( A )" := (scan A) (at level 40).
Notation "print( A )" := (print A) (at level 40).
Notation "CLASS( N ) X" := (declObiect N X) (at level 40).
Notation "-RetString A" := (returnStr A) (at level 40).
Notation "-RetVector A" := (returnVect A) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "X ::=' A" := (assignment1 X A) (at level 50).
Notation "cpy( X , A )" := (sassignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "if( B ){ S }" := (ifthen B S) (at level 45).
Notation "if( B ){ S1 }ELSE{ S2 }" := (ifthenelse B S1 S2) (at level 45).
Notation "While( B ){ S }" := (while B S) (at level 45).
Notation "for*( S1 ; B ; S2 ){ S3 }" := (For S1 B S2 S3) (at level 45).
Notation "struct( NAME ){ S } VAR " := (Struct NAME S VAR) (at level 40).
Notation "CLASS( NAME ){ PRIVATE: S1 PUBLIC: S2 } " := (CLASS NAME S1 S2) (at level 40).
Notation " ( V )( S1 ) " := (function_antet V S1) ( at level 50).
Notation " function( N )( S1 ){ S2 } ":= (function N S1 S2) (at level 44).
Notation " function'( N )(){ S } ":= (function1 N S) (at level 44).
Notation " ctor( N )( S1 ){ S2 } ":= (constructor N S1 S2) (at level 44).
Notation " ctor'( N ){ S } ":= (constructor1 N S) (at level 44).
Notation " ~dtor( N ) ":=(destructor N) (at level 44).
Notation " X ->' Y ":= (obtip X Y) (at level 40).
Notation " X '-> Y ()":= (obfunc X Y) (at level 50).
Notation " X '->> Y (' Z ')":=(obfuncpar X Y Z) (at level 50). 
Notation " lambda( N )[_]( S1 ){ S2 } ":= (simple_lambda N S1 S2) (at level 44).
Notation " lambda( N )[=]( S1 ){ S2 } ":= (passbyvalue_lambda N S1 S2) (at level 44).
Notation " lambda( N )[ S1 ]( S2 ){ S3 } ":= (passvars_lambda N S1 S2 S3) (at level 44).

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
Compute 
-Vector L1 ;;
While( "a" !=' 10 \/' "a"!=' 100){
  if( "a" >=' 50 ){
    if( "a" <' 100){
      PushVar( L1 , "a") ;;
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

Compute
function("newfunc")(-Nat "default"){
      if( "a" <' 100){
      PushVar( L1 , "a") ;;
        "a"::="a" +' 1
      }ELSE{
        "a"::="a" -' 1
      }
}.

Compute
CLASS("NEW_CLASS"){
  PRIVATE:
    -Nat "x";;
    -Vector L0;;
    -Bool "ok" 
  PUBLIC:
    function("newfunc")(-Nat "default"){
      if( "a" <' 100){
      PushVar( L1 , "a") ;;
        "a"::="a" +' 1
      }ELSE{
        "a"::="a" -' 1 ;;
        ("newfunc")("default"::="default" -' 1)
      }
    } ;;
    function'("func")(){
      While( "a" !=' 10 \/' "a"!=' 100){
        if( "a" >=' 50 ){
          if( "a" <' 100){
            PushVar( L1 , "a") ;;
            "a"::="a" +' 1
          }ELSE{
            "a"::="a" -' 1
          }
        }ELSE{
          if("a" >' 10){
            "a"::="a" -' 1
          }ELSE{
            "a"::="a" +' 1 ;; 
            -RetNat "a"
          }
        }
      }
    };;
    ~dtor("NEW_CLASS")
};;
CLASS("NEW_CLASS")"Obiect";;
"Obiect"'->"func"();;
"Obiect"'->>"newfunc"('-Nat "x"');;
-Nat "ceva";; -Nat "newvr" ;; -Nat "newvr2" ;;
scan("ceva") ;; scan("newvr") ;; scan("newvr2") ;;
lambda("lambdasimpla")[_](-Nat "a"){
  -Nat "i";;
  for*("i" ::= 0 ; "i" <=' 10 ; "i"::= "i" +' 1){
    -Nat "j";;
    "j"::= "i" +' "a" ;;
    print( "j" );;
    print("\n")
  }
};;
lambda("lambda_pass_value")[=](-Nat "a"){
  -Nat "i";;
  for*("i" ::= 0 ; "i" <=' 10 ; "i"::= "i" +' 1){
    -Nat "j";;
    "j"::= "i" +' "a" ;;
    "j"::= "j" *' "ceva" ;; "j"::= "j" -' "newvr" ;; "j" ::= "j" /' "newvr2"  ;;
    print( "j" );;
    print("\n")
  }
};;
lambda("lambda_pass_vars")["ceva" ;; "newvr"](-Nat "a"){
  for*("i" ::= 0 ; "i" <=' 10 ; "i"::= "i" +' 1){
    -Nat "j";;
    "j"::= "i" +' "a" ;;
    "j"::= "j" *' "ceva" ;; "j"::= "j" -' "newvr";;
    print( "j" );;
    print("\n")
  }
}
.





