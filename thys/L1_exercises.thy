(*
  Exercises for L1

  Important: this file should be viewed in the Isabelle IDE!
  Download and install Isabelle from https://isabelle.in.tum.de/
  
  In a normal text editor, this file will be largely unreadable, and you cannot interact with it!
*)
section \<open>L1 Exercises\<close>
theory L1_exercises
imports L1_nats_from_basics
begin

hide_const minus

subsection \<open>Minus\<close>
(* Define a function that returns the predecessor of a natural number. For Z, it should return Z.

  Note: this function is not recursive
*)
fun pred :: "nat \<Rightarrow> nat" where


(* Define a function that subtracts natural numbers. 
  If the second operand is greater, the result should be Z.
  
  Use the recursion equation: "a - (S b) = (pred a) - b"

  Hint: do not use "a - (S b) = pred (a - b)", as this is more difficult to reason about (see below)
*)
fun minus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where


(* Prove: *)
lemma diff_self: "minus a a = Z"
  

lemma "minus (plus a b) b = a"  
  
  
(*
  Over which variable have you done the induction for the last lemma? Why?
  Try doing the induction over the other variable. 
    Most likely you'll get stuck, or need complicated auxiliary lemmas, so don't try too long ;)
*)  




  
(*
  Now let's come back to the recursion equation "a - (S b) = pred (a - b)".

  It's implemented by the following function:
*)  
fun minus' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "minus' a Z = a"
| "minus' a (S b) = pred (minus' a b)"  


(* Show that both definitions are equivalent.

  Hint: you'll need to prove an auxiliary lemma about pred and minus!
*)

  

lemma "minus' a b = minus a b"
  


(* Finally, we could have defined minus directly by more complicated pattern matching:*)
fun minus'' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "minus'' Z _ = Z"
| "minus'' a Z = a"
| "minus'' (S a) (S b) = minus'' a b"  


(* Again, show that the definitions are equivalent. 

  Hint: computation induction, and an auxiliary lemma
*)



lemma "minus'' a b = minus a b"



(* Finally, show that subtraction saturates at zero: *)
lemma "le a b \<Longrightarrow> minus a b = Z"

  
  
subsection \<open>Linear Order\<close>  
(* Show that \<open>le\<close> on \<open>nat\<close> is a linear order (sometimes called total order) *)  
lemma "le a b \<or> le b a"



subsection \<open>Times is Associative\<close>
(* Show that times is associative. 
  Hint: the auxiliary lemma you'll need here is a well-known algebraic law you learned in school. 
*)  


  
lemma times_assoc: "times (times a b) c = times a (times b c)" 


(* Finally, show the left-commute lemma required for using associativity and commutativity with
  the simplifier. 
*)


  
lemma times_left_commute: "times a (times b c) = times b (times a c)"




lemmas times_ac = times_assoc times_commute times_left_commute


subsection \<open>Automating Algebra\<close>

(*
  If you arrived here, think of what is required to prove formulas like:

  a * (b + c) * 1 + (a + b + 0) * (c + d) = a*b + a*c + (a+b)*c + (a+b)*d

  Try to assemble a set of rewrite rules that normalize such formulas.  
*)

(* We have started for you. Add (and prove) m ore lemmas here as needed. 
  No need to add lemmas that are already in the simpset.
  
*)
lemmas algebra_simps = plus_ac times_ac 

(*
  When you have enough lemmas, the following test cases should prove automatically. 
*)


lemma "times (plus a (times b c)) (times b c) = plus (times a (times b c)) (times b (times b (times c c)))"
  apply (simp add: algebra_simps)
  done

(* (a+b)\<^sup>2 = a\<^sup>2 + 2ab + b\<^sup>2 *)  
lemma "times (plus a b) (plus a b) = plus (times a a) (plus (times (S(S Z)) (times a b)) (times b b))"  
  apply (simp add: algebra_simps)
  done  

(* At this point, prefix-functions are getting pretty unreadable. Let's define some syntax *)

notation plus (infixl "+" 65)  (* binding to the left, priority 65 *)
notation times (infixl "*" 70) (* binding to the left, priority 70 *)

(* Now, Isabelle will display plus and times as nice infix syntax *)
term "times (plus a b) c"

term "(a+b) * c"


(* Note that this is just a parsing/printing conversion. 
  Isabelle's logic still sees the functions plus and times.
*)

lemma "a+b = plus a b" by (rule refl)


(* Now we can write the formula from the beginning more concisely *)

lemma "a * (b + c) * (S Z) + (a + b + Z) * (c + d) = a*b + a*c + (a+b)*c + (a+b)*d"
  apply (simp add: algebra_simps)
  done  



end
