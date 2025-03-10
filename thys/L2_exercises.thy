theory L2_exercises
imports L2_nats_from_library
begin


  subsection \<open>Mod via Subtraction\<close>  

  text \<open>
    Define a function \<open>mod' n m\<close> that computes the remainder of dividing m by n.
    
    Similar to \<^const>\<open>div'\<close>, repeatedly subtract n from m.
    
    Hint: for termination, complete function to yield \<open>mod' x 0 = x\<close>
  \<close>
  fun mod' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    

  (* Don't forget to remove the function equation from the simpset *)        
  lemmas [simp del] = mod'.simps

  (* Prove: the remainder is less than the divisor*)
  lemma "n\<noteq>0 \<Longrightarrow> mod' m n < n"
    

  (* Prove the well-known equality for div and mod: *)  
  lemma "n*div' m n + mod' m n = m"
    

  



  subsection \<open>Number of Decimal Digits\<close>

  (*
    Implement a function 
      numdec :: nat \<Rightarrow> nat
      
    that returns the number of digits required to represent its argument in decimal.
    
    Idea: count how often you can divide the argument by 10.
    
    Use \<open>value\<close> to test your procedure for a few inputs
  *)  
    
  fun numdec :: "nat \<Rightarrow> nat" where
   
       
  lemmas [simp del] = numdec.simps  

  

  (* Show that your function is sound, i.e., yields enough digits *)      
  lemma "n<10^numdec n"
    

  (* Wait! Have you thought of the fact that the number 0 has one digit? 
    numdec should actually never return 0.
  *)
  lemma numdec_pos: "numdec n \<noteq> 0"  
    
    
              

  (* Show that your function is precise: one less digit wouldn't be sufficient. (Except for 0).
  
    Hint: requires an auxiliary lemma. Many auxiliary lemmas will work, we propose the
      following: under suitable preconditions, 10^n can be written as 10^(n-1)*10.
    
      Don't give up easily after the auxiliary lemma has been applied, but try0 harder!
  *)      
  lemma "n\<noteq>0 \<Longrightarrow> 10^(numdec n - 1) \<le> n"  
              



  subsection \<open>Additive Euclid\<close>

  (*
    We also have the following recursion equations for the gcd:
  
    if a<b:  gcd a b = gcd a (b-a)
    else:    gcd a b = gcd (a-b) b

    Use these to define the recursive function euclid', and prove that
    it computes the gcd. Complete it for the 0-cases as usual.     
  *)  
  
  
  fun euclid' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    
  lemmas [simp del] = euclid'.simps


    

  (* Hint: check out thm gcd_diff1_nat. 
  
    You'll also need a version for the difference in the second operand, 
    i.e., gcd n (m-n) = \<dots>
    
    Prove that as an auxiliary lemma, using thm gcd.commute
  *)
  thm gcd_diff1_nat
  thm gcd.commute
  
  
  lemma "euclid' a b = gcd a b"
  
  

  subsection \<open>\<lfloor>log b x\<rfloor>\<close>
  
  text \<open>Generalize the \<^const>\<open>lg\<close> function to work with any base >=2, and prove it correct \<close>  

  (* Here are a few lemmas that may be helpful in the correctness proof *)
  thm 
    less_eq_div_iff_mult_less_eq 
    div_less_iff_less_mult 
    div_greater_zero_iff 
    mult.commute
  
    
  fun log :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  


  
  subsection \<open>\<lfloor>nth root\<rfloor>\<close>

  text \<open>
    Generalize the \<^const>\<open>sqrt\<close> function to compute roots for any power greater equal 2.
    
    \<open>root_aux p n l h\<close> shall search for the result in the interval l..<h,
    and root p n shall return the rounded-down pth root of n.
  \<close>
    
  function root_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  

  (* Note: add special cases for 
    root p 0 = 0
    root p 1 = 1
    root 1 n = n
  *)  
  definition root :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
    

  (* The following lemmas will be helpful. 
    We'll see later how to find the proofs of many such lemmas automa{t,g}ically.
  *)    
  lemma root_aux1: "\<lbrakk>2\<le>p; 1<n\<rbrakk> \<Longrightarrow> n < n^p" for n :: nat 
    by (metis Suc_1 less_eq_Suc_le power_one_right power_strict_increasing_iff)
  
  lemma root_aux2: "1\<le>p \<Longrightarrow> Suc 0 < Suc (Suc 0) ^ p"
    by (metis One_nat_def lessI less_eq_Suc_le one_less_power)  
    
  thm zero_power  
    
    
  lemma root_correct: "1\<le>p \<Longrightarrow> let r = root p n in r^p\<le>n \<and> n < (r+1)^p"
  

  (* Use value to determine the 13th root of 
    1547728227013226132588676190328398675357735700082353543110029579057296955125743429920510027513732772922469
  *)      

  
  (* But wait: what bounds have you used in root?

    A lower bound of 0 may be fine. But if you used n as upper bound,
    then the function will compute (n div 2)^p. 
    For large p, this is a gigantic value that easily fills up your memory. 
  
    Try 
      value "root 400 (6^400)"
    (A few seconds on my computer, but don't wait too long)
  *)
  
  (*
    Anyway, we can do better by determining an upper bound before the actual computation.
  
    We start with x=1, and then double x as long as x^p\<le>n. After this, we have n<x^p. 
    This needs significantly smaller numbers. And, as a bonus, gives us a lower bound, too:
    just divide the resulting bound by 2 (or remember the last value before doubling).
  *)

  
  (* We have defined the function for you, as the termination argument can get tricky.
  
    We use the fact that 2*y is an upper bound, and then use 2*y-x as decreasing measure.
  *)    
    
  lemma root_upper_bound_aux_term_aux: "x ^ p \<le> y \<Longrightarrow> 1\<le>p \<Longrightarrow> x\<le>y" for x y p :: nat
    by (metis order_trans le0 less_one linorder_not_le self_le_power)
  
  function root_upper_bound_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
    "root_upper_bound_aux p y x = (
      if 1\<le>x \<and> 1\<le>p \<and> x^p \<le> y then root_upper_bound_aux p y (2*x) 
      else x)"
    by pat_completeness auto
  termination 
    apply (relation "measure (\<lambda>(p,y,x). 2*y - x)")
    by (auto dest: root_upper_bound_aux_term_aux) 
  
  lemmas [simp del] = root_upper_bound_aux.simps  

  (* Prove that we compute an upper bound *)    
  lemma root_upper_bound_aux1: "\<lbrakk>1\<le>p; 1\<le>x\<rbrakk> \<Longrightarrow> y < root_upper_bound_aux p y x ^ p"
    

  (* Prove that, when dividing by 2, we get a lower bound (provided the current x is a lower bound) *)  
  (*
    Hint: most likely you will get stuck at a point where the IH is only available
      if "2 ^ p * x ^ p \<le> y". If that holds, you can use the IH. 
      Otherwise, you can subst root_upper_bound_aux.simps again to finish the proof.
  
      To make this case distinction, use 
      apply (cases "2 ^ p * x ^ p \<le> y")
  
  *)
  
  lemma root_upper_bound_aux2: "\<lbrakk>1\<le>p; 1\<le>x; x^p \<le> y\<rbrakk> 
    \<Longrightarrow> (root_upper_bound_aux p y x div 2) ^ p \<le> y"  
    

  (* For better readability of the goals, we define a function that fixes the
    start value. *)      
  definition "root_upper_bound p y \<equiv> root_upper_bound_aux p y 1"  
  
  (* Proof that it computes a valid bound. 
  
    unfold the definition of root_upper_bound, and use what you have already proved.
  *)
      
  lemma root_upper_bound1: "1\<le>p \<Longrightarrow> y < (root_upper_bound p y) ^ p"
    
  
  lemma root_upper_bound2: "\<lbrakk>1\<le>p; 0<y\<rbrakk> \<Longrightarrow> (root_upper_bound p y div 2) ^ p \<le> y"
    

  (* Finally define the root function again. 
    This time, use the more precise upper and lower bounds.
    Also add a special case for root p 0 = 0 
  *)    
  definition root' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  

    
    

  (* Prove your function correct. 
  
    You will need an auxiliary lemma that 0<root_upper_bound p n. 
    Prove a corresponding lemma for root_upper_bound_aux first.
  *)    
  lemma root'_correct: "1\<le>p \<Longrightarrow> let r = root' p n in r^p\<le>n \<and> n < (r+1)^p"
    

  (* Now, you should be able to quickly compute roots, e.g. what is the 
    623rd root (rounded down) of 2^3370?
  *)
      
  
  
  (* If you want to use your verified root program, you can translate it into various PLs.
  
    The translations will declare their own datatype for natural numbers, which is cumbersome to
    work with. In order to translate to the target language's natural number type, you should use
    Isabelle's integer type. We define a constant to do the conversions back and forth:
  *)
  
  definition rooti :: "integer \<Rightarrow> integer \<Rightarrow> integer" where 
    "rooti b c \<equiv> integer_of_nat (root' (nat_of_integer b) (nat_of_integer c))"


  (*
    This can be exported into your favorite functional language:
  *)      
  export_code rooti in SML module_name Root file "../code_export/root.sml"
  export_code rooti in Haskell module_name Root file "../code_export/root_hs"
  export_code rooti in OCaml module_name Root file "../code_export/root.ml"
  export_code rooti in Scala module_name Root file "../code_export/Root.scala"
    

  (*
    e.g., try the following ghci session:
    
    <rio2025-folder>/code_export/root_hs> ghci Root.hs
    Loaded package environment from /home/peter/.ghc/x86_64-linux-9.4.8/environments/default
    GHCi, version 9.4.8: https://www.haskell.org/ghc/  :? for help
    [1 of 1] Compiling Root             ( Root.hs, interpreted )
    Ok, one module loaded.
    ghci> :t rooti
    rooti :: Integer -> Integer -> Integer
    ghci> rooti 13 3893458979352680277349663255651930553265700608215449817188566054427172046103952232604799107453543533

  *)
  

  (* Transferring the correctness theorem to integers is straightforward, if
    you use some fancy Isabelle tools (specifically the transfer and lifting package).
    
    The details are beyond this introductory course, but we present the proof anyway: 
  *)      

  lemma rooti_correct: "\<lbrakk>1\<le>p; 0\<le>n\<rbrakk> \<Longrightarrow> 
      let r = rooti p n in r^(nat_of_integer p)\<le>n \<and> n < (r+1)^(nat_of_integer p)"
    including integer.lifting  
    unfolding rooti_def
    using root'_correct[of "nat_of_integer p" "nat_of_integer n"] 
    apply transfer 
    apply (clarsimp simp: Let_def le_nat_iff)
    by (metis add.commute nat_less_iff of_nat_Suc of_nat_power)
    
  
  
  
  
  
  
  
      
end
