Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import String.
Open Scope string_scope.

Inductive Var : Set :=
| variable : string -> Var.

Scheme Equality for Var.
Coercion variable : string >-> Var.

Definition Var_equality (var1 var2 : Var) : bool :=
  match var1,var2 with
  | variable x, variable y => if (eqb x y) 
                            then true
                            else false
  end. 

Compute Var_equality "aur" "aur".

(*Vectorul este implementat cu ajutorul List*)

Definition Vector := list nat.

Definition add_first (vect : Vector) (valoare : nat): Vector := valoare :: vect. 
Notation "Add( V , Val )" := (add_first V Val) (at level 50). 

Definition length (vect : Vector) : nat := List.length vect.
Notation "Size( V )" := (length V) (at level 50).

Definition last_el (vect : Vector) := List.last vect.
Notation "Last( V )" := (last_el V ) (at level 50). 

Definition remove_ls (vect : Vector) : Vector := List.removelast vect.
Notation "RemoveLast( V )" := (remove_ls V) (at level 50).

Definition index (vect : Vector) (valoare : nat) : nat := List.nth valoare vect 0.
Notation " V [* I *]" := (index V I) (at level 40).



Check [1;2;3].
Compute Size( [1;32;11;9] ).
Compute Last( [1;22;13;91] ).

Definition Vector1 := [1;32;11;9].
Definition Vector2 := Add( Vector1 , 100 ).
Compute Vector2.
Compute Vector2 [* 3 *].
Compute RemoveLast( [1;32;11;9] ).


(* Environment *)

Inductive Value :=
| undef : Value
| structure : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| string_val: string -> Value.


Coercion nat_val : nat >-> Value.
Coercion bool_val : bool >-> Value.
Coercion string_val : string >-> Value.

Scheme Equality for Value.

Definition Env := Var -> Value.

Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x "variable")
    then nat_val 10
    else if(Var_eq_dec x "sir")
          then string_val "mesaj"
          else if(Var_eq_dec x "boolean")
                then bool_val true
                else undef.

Definition empty_env : Env := fun var => undef.

Inductive Struct :=
|structura : Var -> Struct.

Coercion structura : Var >-> Struct.




Definition is_declared (x : Var) (env : Env) :=
  if (Value_beq (env x) undef)
  then false
  else true.

Compute env1 "variable".
Compute env1 "not_a_variable".
Compute is_declared "variable" env1.
Compute is_declared "ms" env1.

Compute env1 "variable".


Definition conv_nat (x : Value) : nat :=
  match x with
  | structure => 999
  | undef => 999
  | bool_val n => 999
  | string_val n => 999
  | nat_val n' => n'
  end.

Compute conv_nat (env1 "variable").

Definition conv_str (x : Value) : string :=
  match x with
  | undef => "!"
  | structure => "!"
  | bool_val n => "!"
  | string_val n => n
  | nat_val n' => "!"
  end.

Compute conv_str (env1 "sir").

Definition conv_bool (x : Value) : bool :=
  match x with
  | undef => false
  | structure => false
  | bool_val n => n
  | string_val n => false
  | nat_val n' => false
  end.

Compute conv_bool (env1 "boolean").

Definition update (env : Env)
           (x : Var) (v : Value) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).




(*ArithExp*)

Inductive ArithExp :=
| avar : Var -> ArithExp
| anum : Value -> ArithExp
| aplus : ArithExp -> ArithExp -> ArithExp
| aminus : ArithExp -> ArithExp -> ArithExp
| amul : ArithExp -> ArithExp -> ArithExp
| adiv : ArithExp -> ArithExp -> ArithExp
| aperc : ArithExp -> ArithExp -> ArithExp.

Coercion avar : Var >-> ArithExp.
Coercion anum : Value >-> ArithExp.

Notation "A -' B" := (aminus A B) (at level 50).
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 40).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (aperc A B) (at level 40).


Fixpoint AEval (a : ArithExp) (env : Env) : Value :=
  match a with
  | avar var => env var
  | anum n' => n'
  | aplus a1 a2 => conv_nat(AEval a1 env) + conv_nat(AEval a2 env)
  | amul a1 a2 => conv_nat(AEval a1 env) * conv_nat(AEval a2 env)
  | aminus a1 a2 =>if( leb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env)))
                       then 0
                       else conv_nat(AEval a1 env) - conv_nat(AEval a2 env)
  | adiv a1 a2 => conv_nat(AEval a1 env) / conv_nat(AEval a2 env)
  | aperc a1 a2 => (Nat.modulo (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env)))

  end.

Compute AEval (16/'4) (env1).
Compute AEval "variable" env1.
Compute AEval ("variable" /' 2)(env1).


(*BoolExp*)
Inductive BoolExp :=
| btrue : BoolExp
| bfalse : BoolExp
| bgt    : ArithExp -> ArithExp -> BoolExp
| bge    : ArithExp -> ArithExp -> BoolExp
| beq    : ArithExp -> ArithExp -> BoolExp
| blt    : ArithExp -> ArithExp -> BoolExp
| ble    : ArithExp -> ArithExp -> BoolExp
| bnot   : BoolExp -> BoolExp
| band   : BoolExp -> BoolExp -> BoolExp
| bxor   : BoolExp -> BoolExp -> BoolExp
| bor    : BoolExp -> BoolExp -> BoolExp.

Notation "A >' B" := (bgt A B)(at level 60).
Notation "A >=' B" := (bge A B)(at level 60).
Notation "A ==' B" := (beq A B)(at level 60).
Notation "A <' B" := (blt A B)(at level 60).
Notation "A <=' B" := (ble A B)(at level 60).
Notation "! A" := (bnot A)(at level 60).
Notation "A &' B" := (band A B)(at level 60).
Notation "A |' B" := (bor A B)(at level 60).
Notation "A ^' B" := (bxor A B)(at level 60).

Fixpoint BEval (b : BoolExp) (env : Env) : Value :=
  match b with
  | btrue => true
  | bfalse => false
  | bnot b' => negb (conv_bool(BEval b' env))
  | bor b1 b2 => orb (conv_bool(BEval b1 env)) (conv_bool(BEval b2 env))
  | bxor b1 b2 => xorb (conv_bool(BEval b1 env)) (conv_bool(BEval b2 env))
  | band b1 b2 => andb (conv_bool(BEval b1 env)) (conv_bool(BEval b2 env))
  | beq a1 a2 => Nat.eqb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env))
  | blt a1 a2 => ltb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env))
  | ble a1 a2 => leb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env))
  | bgt a1 a2 => negb(leb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env)))
  | bge a1 a2 => negb(ltb (conv_nat(AEval a1 env)) (conv_nat(AEval a2 env)))
  end.

Compute BEval (!("x" <' 100)) env1.

Compute AEval "variable" env1.
Compute BEval ("variable" <=' 9) env1.

(*StringExp*)

Inductive StringExp :=
| str_val : string ->StringExp
| str_comp : StringExp -> StringExp -> StringExp
| str_concat : StringExp -> StringExp -> StringExp
| str_len : StringExp -> StringExp.

Coercion str_val : string >-> StringExp.

Notation "strcompare( Str1 , Str2 )" := (str_comp Str1 Str2) (at level 70).
Notation "strconcat( Str1 , Str2 )" := (str_concat Str1 Str2) (at level 50). 
Notation "strlength( Str1 )" := (str_len Str1) (at level 50). 

Check strcompare("abcd" , "abcd").

Fixpoint SEval (s : StringExp) (env : Env) : Value :=
  match s with
  | str_val str => str
  | str_comp s1 s2 => String.eqb (conv_str(SEval s1 env)) (conv_str(SEval s2 env))
  | str_concat s1 s2 => String.append (conv_str(SEval s1 env)) (conv_str(SEval s2 env))
  | str_len s => String.length (conv_str(SEval s env))
  end.

Compute SEval (strlength(strconcat("aer", "aer"))).

(*Stmt*)

Inductive Stmt :=
(*Declarari si assignments*)
| Nat_decl : Var -> Stmt
| Bool_decl : Var -> Stmt
| String_decl : Var -> Stmt
| Vector_decl : Vector -> Stmt
| nat_assignment : Var -> ArithExp -> Stmt
| string_assignment : Var -> StringExp -> Stmt
| bool_assignment : Var -> BoolExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt

(*Structura implementata la nivel de Stmt - notatie*)
| structSTMT : Var -> Stmt -> Stmt
| Struct_init : Var -> Stmt
| Struct_decl : Var -> Var -> Stmt

(*Switch*)
| caseSTMT : ArithExp -> Stmt -> Stmt
| switchSTMT : ArithExp -> Stmt -> Stmt

(*I/O*)
| printSTMT : string -> Stmt
| scanSTMT : Var -> string -> Stmt

(*Instructiuni repetitive si conditionale*)
| ifthen : BoolExp -> Stmt ->Stmt
| ifthenelse : BoolExp -> Stmt -> Stmt -> Stmt 
| while_ : BoolExp -> Stmt -> Stmt.


Inductive Function :=
| call : Stmt -> ArithExp -> Function
| f_return : Value -> Function.

Notation " C ([ A ]) " := (call C A)(at level 80).
Notation "'Return' # R " := (f_return R)(at level 80).

Check Return # 2.

Inductive Format :=
| func_form : Function -> Format
| stmt_form : Stmt -> Format
| func : Function -> Stmt -> Function -> Format
| form_divider : Format -> Format -> Format.
Notation "F1 '$' F2" := (form_divider F1 F2) (at level 99).
Coercion stmt_form : Stmt >-> Format.
Coercion func_form : Function >-> Format.


Notation "X ::= A" := (nat_assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "-nat- V" := (Nat_decl V) (at level 70).
Notation "-bool- V" := (Bool_decl V) (at level 70).
Notation "-string- V" := (String_decl V) (at level 70).
Notation " S --> V " := (Struct_decl S V) (at level 70).
Notation "-vector- V" := (Vector_decl V) (at level 70).
Notation "[ X ] ::= A" := (bool_assignment X A) (at level 80).
Notation "'struct' ( NUME ){ S }" := (structSTMT NUME S) (at level 40).
Notation "copy_string( X , A )" := (string_assignment X A) (at level 80).
Notation " 'print' \\ S " := (printSTMT S) (at level 70).
Notation " 'scan' \\ V \\ S  " := (scanSTMT V S) (at level 70).
Notation "'If' ( B ) 'Then' S1 'Else' S2 " := (ifthenelse B S1 S2) (at level 92).
Notation "'If' ( B ) 'IfThen' S1 " := (ifthen B S1) (at level 92).
Notation "'while' ( Cond ) { S }" := (while_ Cond S)(at level 97).
Notation "'for_' ( I ; Cond ; Pas ) { S }" := (I ;; while_ Cond (S ;; Pas))(at level 97).
Notation "'switch' ( A ) { S } " := (switchSTMT A S)  (at level 90).
Notation " 'case' ( A ) [ S ]  " := (caseSTMT A S)  (at level 90).

Notation " % Call 'begin_' S R 'end_' % " := (func Call S R)(at level 97).



Fixpoint STMTeval (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' =>   match s with
                | Nat_decl var => update env var  0
                | Bool_decl var => update env var false
                | Vector_decl vector => env
                | Struct_init var => update env var structure
                | Struct_decl st v => STMTeval (-nat- "x.diametru" ;; -bool- "x.plin" ;; -string- "x.denumire" ;; Struct_init v ;; Struct_init st ) env gas'
                | String_decl var => update env var ""
                | nat_assignment var exp => update env var (AEval exp env)
                | string_assignment var str => update env var (SEval str env)
                | bool_assignment var b => update env var (BEval b env)
                
                | sequence S1 S2 => STMTeval S2 (STMTeval S1 env gas') gas'
                | ifthen cond S1 => if(conv_bool(BEval cond env))
                                    then STMTeval S1 env gas'
                                    else env
                | ifthenelse cond S1 S2 => if(conv_bool(BEval cond env))
                                            then STMTeval S1 env gas'
                                            else STMTeval S2 env gas'
                | while_ cond S1  => if(conv_bool(BEval cond env))
                                            then STMTeval (S1 ;; (while_ cond S1)) env gas'
                                            else env
                | caseSTMT A X => if(Nat.eqb (conv_nat(env "switch")) (conv_nat(AEval A env)) )
                                 then STMTeval X env gas'
                                 else env
                | switchSTMT A S1 => STMTeval S1 (STMTeval (-nat- "switch" ;; "switch" ::= conv_nat(AEval A env)) env gas') gas'
                | printSTMT str => STMTeval (-string- "print" ;; copy_string("print", str)) env gas'
                | scanSTMT var str =>  STMTeval (copy_string(var, str)) env gas'
                | structSTMT nume S2 => STMTeval S2 (STMTeval (Struct_init nume ) env gas') gas'              
                            
                end
  end.

Definition dec_ex := (STMTeval ( -bool- "bool" ;; 
                              -string- "sir" ;; 
                              -nat- "numar"
                      ) empty_env 100).

Compute dec_ex "numar".
Compute dec_ex "bool".
Compute dec_ex "sir".
Compute dec_ex "not_declared".

Definition decl_ex := (STMTeval ( -bool- "bool" ;; 
                              -string- "sir" ;; 
                              -nat- "numar" ;; 
                              -vector-[11;23] ;;

                               "numar" ::= 12 ;;
                              copy_string("sirul2" , "avion") ;;
                              ["bul"] ::= bfalse ;;
                              
                              If(btrue |' bfalse)
                                Then ["boool"] ::= btrue
                                Else ["boool"] ::= bfalse 

                               ) empty_env 100).
Compute decl_ex "numar".
Compute decl_ex "bool".
Compute decl_ex "sir".
Compute decl_ex "sirul2".
Compute decl_ex "bul".
Compute decl_ex "boool".


Definition while_ex := (STMTeval ( -nat- "nr" ;;
                              "nr" ::= 3 ;;
                              while("nr" <=' 5)
                                {
                                 "nr" ::= 104
                                }


                               ) empty_env 100).

Compute while_ex "nr".

Definition for_ex := (STMTeval ( -nat- "i" ;;
                                 -nat- "sum" ;;
                              for_ ( "i" ::= 2 ; "i" <=' 4 ; "i" ::= "i" +' 1 ) {
                                  "sum" ::= "sum" +' "i"
                                }
                            ) empty_env 100).

Compute for_ex "sum".

Definition switch_ex := (STMTeval ( -nat- "x" ;;
                              switch (6)
                              { 
                              case(2)
                              ["x" ::= 1] ;;
                              case(4)
                              ["x" ::= 7] ;;
                              case(2)
                              ["x" ::= 9]
                              }
                            ) empty_env 100).

Compute switch_ex "x".

Definition print_scan_ex := (STMTeval (   -string- "var" ;;
                                  print \\ "mesaj afisat" ;;
                                  scan \\ "var" \\ "mesaj citit"
                              ) empty_env 100).

Compute print_scan_ex "var".
Compute print_scan_ex "print".

Definition struct_ex := (STMTeval (
  struct ("cerc"){
  -nat- "diametru" ;;
  -string- "denumire" ;;
  -bool- "plin"
  } ;;
   "cerc"-->"x" ;;
  ["x.plin"] ::= btrue 
) empty_env 100).

Compute struct_ex "cerc".
Compute struct_ex "x".
Compute struct_ex "x.plin".
Compute struct_ex "x.denumire".




Definition ex5 :=
  -bool-"global_var"  
$
  -vector-[] 
$
  % -nat- "func" ([ 2 ]) 
      begin_

        for_ ("i" ::=2 ; "i" <=' 6 ; "i" ::= "i" +' 1) {
          "x" ::= "x" +' "i" 
     
          }
        Return # 1
      end_
  %
$
  % -bool- "bool_func" ([ true ])
    begin_
      If("n"<='9)
        Then "i" ::= 2
        Else "i" ::= 1
      Return # 1
    end_
  %
.


