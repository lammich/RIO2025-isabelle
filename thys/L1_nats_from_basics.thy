section \<open>Natural Numbers from Scratch\<close>
theory L1_nats_from_basics
imports Main
begin

(* Deactivate a few standard concepts *)

no_notation plus (infixl "+" 65)
no_notation times (infixl "*" 70)

hide_type nat
hide_const Suc plus times


subsection \<open>Unary Representation of Natural Numbers\<close>

(* Define datatype for natural numbers *)
(*<*)
datatype nat = Z | S nat
(*>*)


(* Use term to typecheck term. Diagnostic commands like term do not affect the state of Isabelle,
  but are very helpful for introspection of what's going on. 
  They are used a lot during proof development, but rarely visible in finished Isabelle theories.  
*)
(*<*)
term "Z"
term "S (S (S Z))"
(*>*)

subsubsection \<open>Addition\<close>

(* Define as recursive function over nat datatype *)
(* Functions can use pattern matching. *)
(*<*)
fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus Z b = b"
| "plus (S a) b = S (plus a b)"
(*>*)

(* Use value to evaluate expressions *)
(*<*)
value "plus (S(S(S Z))) (S Z)"
(*>*)



(* The function definition has proved the function equations as theorems: *)
thm plus.simps

(* Let's show that Z is also a right-neutral element, e.g. plus a Z = a

  This is an induction proof on the structure of a:

  case a=Z: plus Z Z = Z (fun-eqs) .
  
  case a = Suc a'
    IH: plus a' Z = a'
    to show: plus (Suc a') Z = Suc a'
  
      plus (Suc a') Z 
    = Suc (plus a' Z)  (fun-eqs)
    = Suc (a')         (IH)
    . 

    
  Now let's do this proof formally:  
*)



lemma zero_right_neutral: "plus a Z = a"
(* Use only subst and rule *)
(*<*)
  apply (induction a)          (* induction on structure of a *)
  subgoal                      (* Base case *)
    apply (subst plus.simps)   (* subst: rewrite with equation, left to right *)
    apply (rule refl)          (* Solve with reflexivity *) 
    done                       (* Tell Isabelle that this case is done *)
  subgoal premises IH for a    (* Step case *)
    apply (subst plus.simps)   (* rewr with fun-eqs *)
    thm IH                     (* Let Isabelle display theorem. Diagnostic cmd, does not affect proof. *)
    apply (subst IH)           (* rewr with IH *)
    apply (rule refl)          (* reflexivity *)
    done                       (* This case is done *)
  done                         (* Whole proof is done *)
(*>*)  

(*
  Isabelle's simplifier applies a set of rewrite rules, exhaustively, until no more rules match.
  Application is innermost-out, i.e., subterms get rewritten first.
  
  The 'simpset' refers to the default rewriting rules registered in the simplifier.
*)  
  
  
  
(*
  Let's repeat the previous proof, using the simplifier. 
  Note that function equations are automatically added to the simpset. 
  So are the premises of the current subgoal you are proving.
*)
lemma "plus a Z = a"
(*<*)
  apply (induction a)
  apply simp
  apply simp
  done
(*<*)

(* Give lemma a name, and add it to simpset itself *)  
lemma Z_right0[simp]: "plus a Z = a"
  apply (induction a)
  apply simp
  apply simp
  done
  
thm Z_right0  (* We can now refer to this lemma by its name *)
  
(* And the simplifier will rewrite with the lemma *)
lemma "plus (plus a Z) (plus b Z) = plus a b"   
  apply simp
  done

(* Some shortcut notation: by, simp_all *)    
(* by m\<^sub>1 m\<^sub>2 is roughly: apply m\<^sub>1 apply m\<^sub>2 done 
  simp_all - simp on all subgoals
*)

lemma "plus a Z = a" by (induction a) simp_all  




(* Plus is associative *)
lemma plus_assoc: "plus a (plus b c) = plus (plus a b) c"
(*<*)
  (* Let's try induct and simp_all *)
  apply (induction a)
  apply simp_all
  done (* That was easy! *)
(*>*)  
  
(* Experienced Isabelle users typically have a good intuition if a proof is easy, and will just
  try the obvious first, before even understanding the details. 
  
  Only if that fails, you need to dove into more details.
*)
  

(* Plus is commutative.    // call the aux-lemma 'plus_right_S' *)
lemma plus_comm: "plus a b = plus b a"
(*<*)
  apply (induction a)
  apply simp
  apply simp
  oops (* We need an aux-lemma first.  oops cancels the current proof attempt. *)


lemma plus_right_S: "plus a (S b) = S (plus a b)"
  by (induction a) auto

(* Let's try again *)
lemma plus_comm: "plus a b = plus b a"
  apply (induction a)
  apply simp
  apply (simp add: plus_right_S)  (* Add lemma to simpset just for this method application *)
  done

(*>*)  
  
(* Actually, plus_right_S is also a good candidate for the simpset.

  In general, a lemma \<lbrakk>P\<^sub>1;...;P\<^sub>n\<rbrakk> \<Longrightarrow> l=r is a good simpset lemma, if
  
  all of P\<^sub>1,...,P\<^sub>n and r are 'simpler' than l. Simpler here is a 'fluffy' heuristics and not well-defined.
  Depends very much on intuition and experience.
  
  If you carelessly add lemmas to the simpset, rewriting may go on forever, and "apply simp" won't terminate.
*)  
  
lemmas [simp] = plus_right_S (* Add existing lemma to simpset *)

(* From now on, the simplifier will always rewrite with plus_right_S *)

subsection \<open>Multiplication\<close>

fun times :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
(*<*)
  "times Z b = Z"
| "times (S a) b = plus b (times a b)"
(*>*)

(* Analogously to plus *)    
lemma Zmul_right: "times a Z = Z"
(*<*)
  by (induction a) simp_all
(*>*)

(* One is neutral element *)  
  
lemma One_mul_left[simp]: "times (S Z) b = b" by simp (* Why is no induction needed here? *)
lemma One_mul_right[simp]: "times a (S Z) = a" by (induction a) simp_all  


(* Let's prove that times is commutative *)
lemma times_comm: "times a b = times b a"
  (*<*)
  apply (induction a)
  apply (simp_all add: Zmul_right)
  (*>*)
  (* Analogously to plus, we need a lemma to simplify times _ (S _) *)
  oops

lemma times_right_S: "times a (S b) = plus a (times a b)"
  (*<*)
  apply (induction a)
  apply (simp_all)
  apply (simp add: plus_comm)?
  (*>*)
  (* Just plus-comm won't work here: It simply doesn't match! *)
  oops

  
(* Commutativity/associativity setup with the simplifier in Isabelle: 

  associativity always to the right!
  additional rule: a+(b+c) = b+(a+c)
  
  Then, the simplifier will normalize expressions: 
    parenthesis to the right, terms ordered by some linorder on terms. 
  
*)  

lemma plus_ac:
  "plus (plus a b) c = plus a (plus b c)"
  "plus a b = plus b a"
  "plus a (plus b c) = plus b (plus a c)"
  (*<*)
  subgoal by (induction a) simp_all
  subgoal by (rule plus_comm)
  subgoal by (induction a) (simp_all)
  done
  (*>*)

(*
  Typically, assoc-commute lemmas are not added to the default simpset, 
  as they can rewrite terms to unreadability. You add them when you need them.
*)  
  
(* Now we can prove times_right_S, and then times_comm *)  
lemma times_right_S: "times a (S b) = plus a (times a b)"
(*<*)
  apply (induction a)
  apply (simp_all add: plus_ac)
  done
(*>*)
  
lemma times_commute: "times a b = times b a"
(*<*)
  apply (induction a)
  apply (simp_all add: Zmul_right times_right_S)
  done
(*>*)
  

subsection \<open>Comparing Nats\<close>  
  
(* Note: equality is generated automatically by datatype *)
  
thm nat.inject
    
(* Let's define \<le> *)  
  
fun le :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
(*<*)
  "le Z a = True"
| "le (S a) Z = False"
| "le (S a) (S b) = le a b"  
(*>*)

(* \<le> is reflexive *)
lemma le_refl[simp]: "le a a" by (induction a) simp_all

(* \<le> is transitive *)
lemma le_trans: "le a b \<Longrightarrow> le b c \<Longrightarrow> le a c" 
  apply (induction a) 
  apply simp_all 
  (* Something is wrong here. b and c are fixed, but when a get's smaller, also 
  b might have got smaller. *)

  (* We can get a little bit further by a case distinction on b *)  
  apply (cases b) (* Case distinction over datatype: Z or S _ *)
  apply simp_all 
  (* The IH only holds for fixed, b (now b = Suc _). We're stuck. *)
  oops

(* Multiple ways out here: *)
    
(* 1) Generalize over b (and c). E.g.: *)
lemma le_trans: "\<And>b c. le a b \<Longrightarrow> le b c \<Longrightarrow> le a c" 
  (*<*)
  apply (induction a) 
  apply simp_all 
  subgoal for a b c
    apply (cases b) 
    apply simp_all
    apply (cases c) 
    apply simp_all 
    done
  done  
  (*>*)

(* This is so common, that induct supports it directly: *)
lemma "le a b \<Longrightarrow> le b c \<Longrightarrow> le a c"  
  apply (induction a arbitrary: b c) 
  apply simp_all 
  subgoal for a b c
    apply (cases b) 
    apply simp_all
    apply (cases c) 
    apply simp_all 
    done
  done  
  
(* 2) Use induction rule generated by fun *)
lemma "le a b \<Longrightarrow> le b c \<Longrightarrow> le a c"  
  apply (induction a b arbitrary: c rule: le.induct) (* Still need to generalize over c *)
  (*<*)
  apply simp_all 
  subgoal for a b c
    apply (cases c) apply simp_all 
    done
  done
  (*>*)

(*
  Every function generates an induction rule, that matches the patterns used in the function equations.
  
  Heuristics: use the induction rule for the function with the most complex pattern in your lemma.
    If all functions are primitive-recursive, e.g., match the cases of a single datatype, induction
    on the datatype can be used.
    
    If there are multiple functions with complex patterns, and there is no most complex one,
    advanced techniques are needed, like induction on a well-founded relation.


  Terminology:
    structural induction: induction on structure of datatype
    computation induction: induction on recursion patterns of function
        
*)  
  
lemma le_antisym: "le a b \<Longrightarrow> le b a \<Longrightarrow> a=b"  
(*<*)
  apply (induction a b rule: le.induct)
  apply simp_all
  (* At this point, we can either do another case distinction, or prove an auxiliary lemma *)
  subgoal for a
    apply (cases a) apply simp_all
    done
  done  
(*>*)  

(*<*)
(* Aux-lemma would be *)
lemma le_Z_iff_Z[simp]: "le a Z = (a=Z)"  
  by (cases a) simp_all

(* Now the proof goes easily *)    
lemma "le a b \<Longrightarrow> le b a \<Longrightarrow> a=b"  
  by (induction a b rule: le.induct) simp_all

(*>*)
  

(*<*)  
lemma plus_mono_aux: "le b (plus a b)"
  apply (induction b)
  apply (simp_all)
  done
(*>*)
    
lemma plus_left_mono: "le a a' \<Longrightarrow> le (plus a b) (plus a' b)"
(*<*)  
  apply (induction a a' rule: le.induct)
  apply (simp_all add: plus_mono_aux)
  done
(*>*)

lemma plus_mono: "le a a' \<Longrightarrow> le b b' \<Longrightarrow> le (plus a b) (plus a' b')" 
(* User trans, comm, subst, subst (n), etc to derive lemma from existing thms *)
(*<*)  
  apply (rule le_trans)
  apply (rule plus_left_mono)
  apply assumption
  
  apply (subst plus_comm)
  (*apply (subst plus_comm)*) (* Oops, that just reverted our previous subst. We need more control where to subst! *)
  apply (subst (2) plus_comm)
  apply (rule plus_left_mono)
  apply assumption
  done 
(*>*)
  

(*
  Summary (basic nat)

  datatype, fun, induction, cases
    define recursive data and computations, and reason about them

  subst, simp
    rewrite equal things, left to right
  
  rule, assumption
    resolution ( \<lbrakk> A\<Longrightarrow>B; C\<Longrightarrow>A \<rbrakk>  \<Longrightarrow>  C\<Longrightarrow>B  )
    uses unification behind the scenes.
  

*)  
  
  
end
