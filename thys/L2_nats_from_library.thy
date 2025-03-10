section \<open>Natural numbers from Isabelle's library\<close>
theory L2_nats_from_library
imports Main (* Main contains natural numbers *)
  "HOL-Library.Code_Target_Nat" (* \<leftarrow> we'll see what that does later *)
begin

  typ nat
  term 0 term Suc

  term "42::nat"
  
  (* A lot of things pre-defined, and simplifier set up *)
  
  lemma "a+b+c \<le> Suc a + 2*b + c" by simp
  
  lemma "a\<noteq>0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> a+b+c \<le> a + a*b + c" for a b c :: nat
    by simp


  subsection \<open>Sum of first n odd numbers\<close>  
        
  (* Sum up the first n odd numbers? What will you get? *)
    
  (*<*)
  fun sq where
    "sq 0 = 0"
  | "sq (Suc n) = 2*n+1 + sq n"  
    
  lemma "sq n = n*n"
    apply (induction n)
    by simp_all

  (*>*)  

  subsection \<open>Division via subtraction.\<close>  
  
  
  fun div' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  (* Complete function for div 0! *)
  (*<*)
    "div' m n = (if m < n \<or> n=0 then 0 else 1 + div' (m-n) n)"
  (*>*)  
  
  (*
    Functions in Isabelle must always terminate. 
      Otherwise we could derive, e.g., 0=1 from the function equation f x = f x + 1

    Standard trick that often works: 
      artificially complete function for non-terminating argument values
  *)
  
     
  (*
    Note: when the function equation does not contain pattern matching,
    you typically do not want it into the simpset: the simplifier may
    unfold it over and over again, not terminating and filling your memory with 
    bigger and bigger terms.
  *)       
  lemmas [simp del] = div'.simps

  
  lemma "n * div' m n \<le> m"
    (* Will need auto. try0! *)
  (*<*)
    apply (induction m n rule: div'.induct)
    apply (subst div'.simps)
    apply simp_all 
    apply auto
    done
  (*>*)  
  
  (*
    Quick overview of automated methods:
    
      simp, simp_all:  only rewriting
      
      auto:  rewriting + logic, applied to all subgoals

      \<Longrightarrow> simp, simp_all, and auto will leave the parts of the 
          goal they cannot solve to the user. This is incredibly useful for proof development.
      
      All the methods below either solve the subgoal or fail:       
            
      blast: tableaux prover, no rewriting

      And many more, e.g.
      
      fastforce, force, linarith, etc   
  
      
    As Isabelle user, you'll get a feeling which method to use, or you just try0 them all.
  *)
  

  lemma "n * div' m n + n > m"
    quickcheck (* quickcheck generates and evaluates test-cases for a proposed theorem.
      Only works if statement is executable. 
      
      Very useful during proof writing. You should enable auto-quickcheck in your options!
      *)
    oops
  
  lemma "n\<noteq>0 \<Longrightarrow> n * div' m n + n > m"
    (*<*)
    apply (induction m n rule: div'.induct)
    apply (subst div'.simps)
    apply auto 
    done
    (*>*)
  


  subsection \<open>Logarithm via repeated division\<close>        
       
  (* lg n shall compute \<lfloor>log 2 n\<rfloor> *)   
  fun lg :: "nat \<Rightarrow> nat" where
    (*<*)
    "lg n = (if n<2 then 0 else 1 + lg (n div 2))"
    (*>*)
    
  lemmas [simp del] = lg.simps  

  (* We show that 2^lg n \<le> n, and n < 2^(lg n + 1) *)
  lemma lg_bounds: "n\<noteq>0 \<Longrightarrow> let r = lg n in 2^r \<le> n \<and> n < 2^(r+1)"
  (*<*)
    apply (induction n rule: lg.induct)
    apply (subst lg.simps)
    apply (auto simp: Let_def)
    done
  (*>*)

  (* We could have shown that lg n is the greatest number r with 2^r \<le> n directly *)  
  lemma "n\<noteq>0 \<Longrightarrow> lg n < r \<Longrightarrow> n < 2^r"
    apply (induction n arbitrary: r rule: lg.induct)
    apply (subst (asm) (2) lg.simps)
    apply (auto simp: Let_def split: if_splits)
    (* However, that get's a  bit more complicated. Not now. *)
    oops
    
  (* The reason why that proof gets complicated is, that we are trying to prove many things
      at once: the bound on lg, and monotonicity of 2^_.
    
    Typically, you will try to keep things as simple as possible, 
    and rather prove some auxiliary lemmas first.
  *)  

  lemma power2_mono_aux: "n < 2*2^r \<Longrightarrow> n < 2*2^(r+d)" for n r d :: nat
    by (induction d) auto
      
  lemma nat_less_add: "a<b \<Longrightarrow> \<exists>d. b = a + 1 + d" for a b :: nat by presburger
      
    
  lemma "n\<noteq>0 \<Longrightarrow> lg n < r \<Longrightarrow> n < 2^r"
    apply (frule nat_less_add)
    apply clarsimp
    apply (rule power2_mono_aux)
    (* Note: the lg_bounds lemma is nice to read, but not nice to use! *)
    using lg_bounds[of n] 
    apply (simp add: Let_def)
    done 

  (* The following lemmas are easier to use: *)  
  lemma lg_lbound: "n\<noteq>0 \<Longrightarrow> 2^lg n \<le> n"
    using lg_bounds by metis   
    
  lemma lg_ubound: "n\<noteq>0 \<Longrightarrow> n < 2*2^(lg n)"
    using lg_bounds[of n] by (simp add: Let_def)    

  (* Note: The simplifier will rewrite 2^(x+1) to 2*2^x, thus we use this form in the above lemma *)    

  (* Now let's try again to prove the 'greatest' lemma: *)        
  lemma "n\<noteq>0 \<Longrightarrow> lg n < r \<Longrightarrow> n < 2^r"
    apply (drule nat_less_add)   (* drule: implication in premises *)
    apply clarsimp
    apply (rule power2_mono_aux)
    apply (rule lg_ubound)
    by simp
    
  (* A more experienced user would write *)
  lemma "n\<noteq>0 \<Longrightarrow> lg n < r \<Longrightarrow> n < 2^r"
    by (auto dest: nat_less_add simp: power2_mono_aux lg_ubound)
        
  subsubsection \<open>Efficient Evaluation\<close>        

  (* Evaluating quickly gets slow. 
    Isabelle is computing with an inefficient representation of nat.

    Include Code_Target_Nat to use ML's arbitrary precision integers instead.
  *)

  value "lg 9181"  
  (*  
  value "lg' 8379813467386128327462137863217856821761736478213568723"
  *)
    
    
    
    
    
  subsection \<open>Euclid's algorithm\<close>    
          
  (*<*)
  lemma euclid_term_aux[termination_simp]: "0<a \<Longrightarrow> a<b \<Longrightarrow> b mod a < b" for a :: nat
    apply (rule order.strict_trans)
    apply (rule mod_less_divisor)
    apply assumption
    apply assumption
    done
  (*>*)
  
  fun euclid :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "euclid a b = (
      if a=b \<or> a=0 then b 
      else if b=0 then a
      else if a<b then euclid a (b mod a)
      else euclid (a mod b) b  
      )"

  (* Sometimes, the function package needs a little help to prove a function terminating.
  
    One possibility is to add an additional lemma to the simpset used by the function package:
    Use the [termination_simp] attribute for that.
    
    To prove the auxiliary lemma, use find_theorems to find the relevant lemma names 
  *)    
      

  (*
    find_theorems is another very useful diagnostic command for proof development.
    It will search all available theorems (in imported theories only) for a certain pattern.
  *)
  
  find_theorems "_ mod _ < _"
  
  find_theorems "_ mod ?d < ?d"  (* Use ?-variables in patterns *)
  
  find_theorems "_ mod d < d"    (* Do not use 'normal' variables, they won't match anything *)

  find_theorems "_<(_::nat)"  (* You can add type annotations.*) 
  
  find_theorems "_<(_::nat)" name: "induct"  (* And constraints on the theorem name *) 
          
  find_theorems "_<(_::nat)" name: "in*ct"  (* Wildcards *) 

  find_theorems -"(+)" -"(*)" name: comm  (* Negation of criterion *)
  
        
  lemmas [simp del] = euclid.simps    

  
  (*<*)        
  lemma euclid_aux1: "a\<noteq>0 \<Longrightarrow> gcd a (b mod a) = gcd a b" for a b :: nat
    apply (subst (2) gcd.commute)
    apply (subst (2) gcd_non_0_nat)
    by simp_all
    
  lemma euclid_aux2: "b\<noteq>0 \<Longrightarrow> gcd (a mod b) b = gcd a b" for a b :: nat 
    apply (subst (2) gcd_non_0_nat)
    apply (simp_all add: gcd.commute)
    done
  (*>*)  
  
  lemma "euclid a b = gcd a b"    
  (*<*)        
    apply (induction a b rule: euclid.induct)
    apply (subst euclid.simps)
    apply (simp add: euclid_aux1 euclid_aux2)
    done    
  (*>*)  
  


  subsection \<open>Binary Search for inverse of monotone function: sqrt\<close>
  
  (*
    We are looking for r with r\<^sup>2 \<le> n < (r+1)\<^sup>2
  
    Idea: start with lower and upper bound, such that
      
    l<h, l\<^sup>2 \<le> n, n < h\<^sup>2
    
    In each step:
    
    compute m = (l+h) div 2
  
    if m\<^sup>2 \<le> n: continue with m..<h
    else: continue with l..<m
  
    if l+1=h, return l

    
    Termination: h-l gets smaller in each step.  
  *)
  

  function sqrt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  (*<*)
    "sqrt_aux n l h = (
      if l+1\<ge>h then l
      else 
        let m = (l+h) div 2 in
        if m*m \<le> n then sqrt_aux n m h
        else sqrt_aux n l m
    )"  
    by pat_completeness auto
  termination 
    apply (relation "measure (\<lambda>(n,l,h). h-l)")
    apply simp_all
    done 
  (*>*)  

  (*
    When the automatic termination prover in fun does not succeed, and you don't see
    any obvious [termination_simp] lemmas to add, you can always resort to proving termination 
    manually. For this, you must specify a well-founded relation. 
    
    Typically, you specify a measure, i.e., a function from the arguments to nat that gets
    smaller in each recursive call.
    
    As a nat can only get smaller finitely many times, the recursion must eventually terminate.
  *)
    
  lemmas [simp del] = sqrt_aux.simps  

  (*<*)
  lemma sqrt_aux_aux: "l<h \<Longrightarrow> h\<le>Suc l \<Longrightarrow> h = l+1" by simp
  (*>*)
  lemma sqrt_aux_correct: "l*l \<le> n \<Longrightarrow> n < h*h \<Longrightarrow> l<h 
    \<Longrightarrow> let r = sqrt_aux n l h in r*r\<le>n \<and> n<(r+1)*(r+1)"
  (* Note: aux-lemma required for termination case, to get h=l+1 *)  
  (*<*)
    apply (induction n l h rule: sqrt_aux.induct)
    apply (subst sqrt_aux.simps)
    subgoal for n l h
      by (auto simp: Let_def dest: sqrt_aux_aux)
    
    done
  (*>*)

  (* Now we need bounds to initialize binary search *)
    
  lemma "1<n \<Longrightarrow> n < n*n" for n :: nat by simp
  
  (* Definition: non-recursive function. Not put into simpset by default.
  
    Use definitions unless you need recursion or pattern-matching!
  *)
  definition "sqrt n \<equiv> if n=0 then 0 else if n=1 then 1 else sqrt_aux n 0 n"
  
  lemma sqrt_correct: "let r = sqrt n in r*r\<le>n \<and> n < (r+1)*(r+1)"
    unfolding sqrt_def (* Unfold definition. simp add: xxx_def works in most cases, too. *)
    using sqrt_aux_correct
    by simp
  
  (* Show effect of HOL-Library.Code_Target_Nat! *)
  value "sqrt 99"


  subsection \<open>Exporting Code\<close>

  (*
    Functions defined in Isabelle can be exported to your favorite functional PL.
    Currently Isabelle supports SML, OCaml, Haskell, and Scala. 
    There is an external library for Go.
  *)
  

  export_code 
    euclid lg sqrt 
    integer_of_nat nat_of_integer
    in Haskell module_name VerNumLib file "../code_export/VerNumLib"
    
  (* This creates a folder VerNumLib,
    with a file VerNumLib.hs, defining the module VerNumLib, which exports 
    the specified functions (and prerequisite types)
    
    module VerNumLib(Nat, Num, integer_of_nat, nat_of_integer, lg, sqrt, euclid)
    
    (Note, the type Num is not really needed. Exporting it is a quirk in the code-generator)
  *)
  
  (*
    Let's test the code:

    .../VerNumLib$ ghci VerNumLib.hs
    ghci> :t sqrt
    sqrt :: Nat -> Nat

    ghci> sqrt 67

    <interactive>:2:6: error:
      • No instance for (Prelude.Num Nat) arising from the literal ‘67’
   
    ghci> sqrt (nat_of_integer 67)
    
    <interactive>:4:1: error:
        • No instance for (Prelude.Show Nat)
            arising from a use of ‘Prelude.print’
        • In a stmt of an interactive GHCi command: Prelude.print it
        
    ghci> integer_of_nat (sqrt (nat_of_integer 67))
    8
      

    Instead of Haskell's integer type, the functions use their own type Nat 
    (which is just a wrapper around integer, due to Code_Target_Nat).
    
    This can get cumbersome to work with. You can either define the wrapping and unwrapping
    on Haskell's side:
    
    ghci> sqrti = integer_of_nat . sqrt . nat_of_integer 
    ghci> sqrti 67
    8
            
  
    Or in Isabelle:
  *)  

  definition "euclidi x y \<equiv> integer_of_nat (euclid (nat_of_integer x) (nat_of_integer y))"
  definition "lgi x \<equiv> integer_of_nat (lg (nat_of_integer x))"
  definition "sqrti x \<equiv> integer_of_nat (sqrt (nat_of_integer x))"
    
  
  export_code 
    euclidi lgi sqrti 
    in Haskell module_name VerNumLib file "../code_export/VerNumLib2"
  
  (*
    .../VerNumLib2$ ghci VerNumLib.hs 
    ghci> :t sqrti
    sqrti :: Integer -> Integer
    ghci> sqrti 67
    8
    ghci> lgi 67
    6
    ghci> euclidi 672687216 673648712
    8
  *)
  
    
          
    
    
    
          

end
