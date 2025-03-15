theory exam
imports Main "HOL-Library.Code_Target_Nat"
begin

(*
  RIO 2025 Summer School. Isabelle Course. Exam.
  
  Complete the definitions, lemmas, and proofs in this file as described in the comments,
  and send the completed file to p.lammich@utwente.nl, 
  mentioning "RIO2025 Isabelle exam" and your name in the subject,
  no later than April 13, 2025 23:59, AoE 
  
  
  Grading: 4 points per section, for a total of 24 points. Scale:
  
  Points \<ge>:  0  2  4  6  8  10 13 16 20      20 and bonus question solved                              
  Grade \<ge>:   1  2  3  4  5  6  7  8  9       10

  The bonus question is at end of question 5  
*)


section \<open>1) Explode (easy)\<close>

(* The folowing function is commonly seen in funcional programming libraries. 
  It converts a list to a list of singleton lists of its elements *)
  
fun explode :: "'a list \<Rightarrow> 'a list list" where
  "explode [] = []"
| "explode (x#xs) = [x] # explode xs"   

(* Prove: *)

lemma explode_append[simp]: "explode (xs@ys) = explode xs @ explode ys"
  

(* An experienced functional programmer would write the explode-function more compactly. Prove: *)
lemma "explode xs = map (\<lambda>x. [x]) xs"


(* What is a simpler way of saying concat (explode xs)? Find the RHS and prove *)
lemma concat_explode[simp]: "concat (explode xs) = insert_sensible_value_here"  
  oops
  

  
  
section \<open>2) Map, tail recursively (easy..medium)\<close>

(*
  The following is a tail recursive version of map, that only uses Cons operations. 
  That is, a compiler will translate that to a loop (no stack memory required for tail recursion),
  and the loop iteration will be constant time.
  
  Prove that it is the same as map!
  
  Hint: prove two auxiliary lemmas first, namely:
  
    fold (#) xs [] = rev xs
    fold (\<lambda>x ys. f x # ys) xs [] = rev (map f xs)
  
  then your main goal can be solved easily.  
*)
definition "maptr f xs = fold (#) (fold (\<lambda>x ys. f x # ys) xs []) []"


    
lemma "maptr f xs = map f xs"
  

section \<open>3) Duplicate List (easy..medium)\<close>
(* The following function duplicates every element in a list *)  
fun dupl :: "'a list \<Rightarrow> 'a list" where
  "dupl [] = []"
| "dupl (x#xs) = x#x#dupl xs"  

value "dupl ''abc''"

(* State and prove the append lemma for dupl: *)
lemma dupl_append[simp]: "insert_statement_here" oops

  

(* State and prove an equation for length (dupl xs). The rhs shouldn't contain dupl anymore*)

lemma "length (dupl xs) = insert_term_here"  oops

  

(* When the list is only made up of the same elements, instead of duplicating each element, we can just
  append the list to itself! Prove:  *)  
lemma "dupl (replicate n x) = replicate n x @ replicate n x"
(* Hint: auxiliary lemma about replicate required. But it's in he library, so use find_theorems. *)
  

(* Again, an experienced functional programmer would write dupl more compactly.
  Express dupl in terms of concat, map, and replicate, and prove your statement.
*)

lemma "dupl xs = insert_term_here" oops

(* Note: do add the parameter xs to the left hand side, 
    even if it can be written more elegantly as "dupl = \<dots>". 
    Otherwise, you need extra steps in your proof before you have something to do induction on.
    
   Hint: to evaluate terms that contain natural number numerals in the simplifier, you have to add
    the fact eval_nat_numeral, e.g. *)
lemma "replicate 2 x = [x,x]" by (simp add: eval_nat_numeral)  
  

  
  

section \<open>4) 2^n (medium)\<close>

(* Implement a recursive function for 2^n, exploiting the laws:
  2^0 = 1
  2^(n+1) = 2 * 2^n
*)
fun power2 :: "nat \<Rightarrow> nat" where


(* Prove the well-known law:  (easy)  *)
lemma power2_add: "power2 (a+b) = power2 a * power2 b"
  

  

(* Prove that 2^n is monotonic.   (medium)
  Hint: you'll most likely need an aux-lemma and an extra case distinction *)    
lemma "n\<le>m \<Longrightarrow> power2 n \<le> power2 m"

  
  
section \<open>5) Lists with fixed length and element sum (medium..hard)\<close>

(* The following (scary-looking) function generates the set of all lists with length l and sum s: *)
fun fixed_ls :: "nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "fixed_ls 0 s = (if s=0 then {[]} else {})"
| "fixed_ls (Suc l) s = { s'#xs | s' xs. s'\<le>s \<and> xs \<in> fixed_ls l (s-s') }"    

(* But don't get scared too much: The most complicated part is the set comprehension. It has the form:

  { term | vars. condition }
  
  where vars specifies the bound variables in term over which the comprehension should be done.
  In our case, it's all lists of the form s'#xs, such that s'\<le>s and xs \<in> \<dots>
  i.e., the comprehension goes over the variables s' and xs. 
  

  Moreover, Isabelle's library has good support for proving with set comprehensions, so you shouldn't
  struggle too much to prove the above claim about what fixed_ls does:
*)



(* Show that fixed_ls is the claimed set: *)
lemma fixed_ls: "fixed_ls l s = { xs. length xs = l \<and> sum_list xs = s }"
(*
  The set comprehension { x. condition } is short for { x | x. condition }
  
  Hint: to prove this lemma, you best to prove it's two directions separately.
*)
  apply auto
  (* Use the subgoals here as hint what auxiliary lemmas to prove. 
    But clean up your proof afterwards to not contain more methods after auto!
  *)

      
  

subsection \<open>Bonus question (extra hard!)\<close>
(* How many such lists do exists. Find a nice formula and prove it correct. 
  Hint: there is a short formula based on binomial coefficients, written in Isabelle as "n choose k".

  You only need to solve that question if you want a 10 (see grading scale above)  
*)

lemma "card { xs. length xs = l \<and> sum_list xs = s } = find_nice_formula" oops 

      
  
  
section \<open>6) Run-Length Encoding (hard)\<close>  

(*
  Run-length encoding is a compression technique that summarizes runs of equal elements.
  
  For example, the encoding of [a,b,b,b,c,c] is [ (1,a),(3,b),(2,c) ]

  Start with a function count_prefix x xs, that counts how many x-elements are at the beginning of xs (maybe 0).
  Then implement the decoder and encoder, and show them correct!
  
*)


fun count_prefix :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where


definition rld :: "(nat \<times> 'a) list \<Rightarrow> 'a list" 
  
  
(* Test: *)
value "rld [(3,a),(4,b)] = [a, a, a, b, b, b, b]"  
    

  


fun rle :: "'a list \<Rightarrow> (nat\<times>'a) list" where
  

(* Test *)
value "rle ''aaabbbbcccd'' = [(3, CHR ''a''), (4, CHR ''b''), (3, CHR ''c''), (1, CHR ''d'')]"


lemma "rld (rle xs) = xs"
  
  

end
