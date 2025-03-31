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
    (*<*)
    "mod' m n = (if m < n \<or> n=0 then m else mod' (m-n) n)"
    (*>*)

  (* Don't forget to remove the function equation from the simpset *)        
  lemmas [simp del] = mod'.simps

  (* Prove: the remainder is less than the divisor*)
  lemma "n\<noteq>0 \<Longrightarrow> mod' m n < n"
  (*<*)
    apply (induction m n rule: mod'.induct) 
    apply (subst mod'.simps)
    by simp
  (*>*)  

  (* Prove the well-known equality for div and mod: *)  
  lemma "n*div' m n + mod' m n = m"
  (*<*)
    apply (induction m n rule: div'.induct)
    apply (subst div'.simps)
    apply (subst mod'.simps)
    apply (simp add: algebra_simps)
    done
  (*>*)  

  (*<*)
  (* Solution with one function *)      
  fun divmod' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
    "divmod' m n = (if m < n \<or> n=0 then (0,m) else let (q,r) = divmod' (m-n) n in (1 + q, r))"

  lemmas [simp del] = divmod'.simps  
      
  lemma "let (q,r) = divmod' m n in q*n + r = m" 
    apply (induction m n rule: divmod'.induct) 
    apply (subst divmod'.simps)
    apply (auto simp: algebra_simps)
    done
  (*>*)



  subsection \<open>Number of Decimal Digits\<close>

  (*
    Implement a function 
      numdec :: nat \<Rightarrow> nat
      
    that returns the number of digits required to represent its argument in decimal.
    
    Idea: count how often you can divide the argument by 10.
    
    Use \<open>value\<close> to test your procedure for a few inputs
  *)  
    
  fun numdec :: "nat \<Rightarrow> nat" where
  (*<*)
    "numdec n = (if n<10 then 1 else 1 + numdec (n div 10))"
  (*>*) 
       
  lemmas [simp del] = numdec.simps  

  (*<*)
  value "numdec 0"
  value "numdec 9"
  value "numdec 10"
  value "numdec 123"
  (*>*)

  (* Show that your function is sound, i.e., yields enough digits *)      
  lemma "n<10^numdec n"
  (*<*)
    apply (induction n rule: numdec.induct)
    apply (subst numdec.simps)
    apply (auto)
    done
  (*>*)  

  (* Wait! Have you thought of the fact that the number 0 has one digit? 
    numdec should actually never return 0.
  *)
  lemma numdec_pos: "numdec n \<noteq> 0"  
  (*<*)
    apply (induction n rule: numdec.induct)
    apply (subst numdec.simps)
    apply simp
    done
  (*>*)  
    
  
  (*<*)
  
  lemma decr_exponent_aux: "n\<noteq>0 \<Longrightarrow> 10^n = 10^(n-Suc 0) * (10::nat)"
    apply (cases n) apply auto done  
  
  lemma numdec_lower_aux: "n\<noteq>0 \<Longrightarrow> 10^(n-Suc 0) \<le> k div 10 \<Longrightarrow> 10^n \<le> k" for n k :: nat  
    by (cases n) simp_all
    
    
  (*>*)            

  (* Show that your function is precise: one less digit wouldn't be sufficient. (Except for 0).
  
    Hint: requires an auxiliary lemma. Many auxiliary lemmas will work, we propose the
      following: under suitable preconditions, 10^n can be written as 10^(n-1)*10.
    
      Don't give up easily after the auxiliary lemma has been applied, but try0 harder!
  *)      
  lemma "n\<noteq>0 \<Longrightarrow> 10^(numdec n - 1) \<le> n"  
  (*<*)
    apply (induction n rule: numdec.induct)
    apply (subst numdec.simps)
    subgoal for n
      apply (clarsimp simp: numdec_pos decr_exponent_aux) by linarith
    done

  (* alternative aux-lemma *)        
  lemma "n\<noteq>0 \<Longrightarrow> 10^(numdec n - 1) \<le> n"  
    apply (induction n rule: numdec.induct)
    apply (subst numdec.simps)
    subgoal for n
      apply (clarsimp simp: numdec_lower_aux numdec_pos)
      done
    done
    
    
  (*>*)            



  subsection \<open>Additive Euclid\<close>

  (*
    We also have the following recursion equations for the gcd:
  
    if a<b:  gcd a b = gcd a (b-a)
    else:    gcd a b = gcd (a-b) b

    Use these to define the recursive function euclid', and prove that
    it computes the gcd. Complete it for the 0-cases as usual.     
  *)  
  
  
  fun euclid' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  (*<*)
    "euclid' a b = (
      if a=b \<or> b=0 then a 
      else if a=0 then b 
      else if a<b then euclid' a (b-a) else euclid' (a-b) b)"
  (*>*)  
  lemmas [simp del] = euclid'.simps


  (*<*)        
  lemma gcd_diff1_nat': "a \<le> b \<longrightarrow> gcd a (b - a) = gcd a b" for a b :: nat
    apply (subst gcd.commute)
    apply (simp add: gcd_diff1_nat)
    apply (simp add: gcd.commute)
    done
  (*>*)  

  (* Hint: check out thm gcd_diff1_nat. 
  
    You'll also need a version for the difference in the second operand, 
    i.e., gcd n (m-n) = \<dots>
    
    Prove that as an auxiliary lemma, using thm gcd.commute
  *)
  thm gcd_diff1_nat
  thm gcd.commute
  
  
  lemma "euclid' a b = gcd a b"
  (*<*)
    apply (induction a b rule: euclid'.induct)
    apply (subst euclid'.simps)
    apply (simp add: gcd_diff1_nat gcd_diff1_nat')
    done
  (*>*)
  

  subsection \<open>\<lfloor>log b x\<rfloor>\<close>
  
  text \<open>Generalize the \<^const>\<open>lg\<close> function to work with any base >=2, and prove it correct \<close>  

  (* Here are a few lemmas that may be helpful in the correctness proof *)
  thm 
    less_eq_div_iff_mult_less_eq 
    div_less_iff_less_mult 
    div_greater_zero_iff 
    mult.commute
  
    
  fun log :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  (*<*)
    "log b n = (if b<2 \<or> n<b then 0 else 1 + log b (n div b))"
    
  lemmas [simp del] = log.simps  

  (* We show that b^log b n \<le> n, and n < b^(log b n + 1) *)
  lemma lg_bounds: "\<lbrakk>n\<noteq>0; 2\<le>b\<rbrakk> \<Longrightarrow> let r = log b n in b^r \<le> n \<and> n < b^(r+1)"
    apply (induction b n rule: log.induct)
    apply (subst log.simps)
    apply (auto simp: Let_def less_eq_div_iff_mult_less_eq 
            div_less_iff_less_mult div_greater_zero_iff mult.commute)
    done
  
  (*>*)


  
  subsection \<open>\<lfloor>nth root\<rfloor>\<close>

  text \<open>
    Generalize the \<^const>\<open>sqrt\<close> function to compute roots for any power greater equal 2.
    
    \<open>root_aux p n l h\<close> shall search for the result in the interval l..<h,
    and root p n shall return the rounded-down pth root of n.
  \<close>
    
  function root_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  (*<*)
    "root_aux p n l h = (
      if l+1\<ge>h then l
      else 
        let m = (l+h) div 2 in
        if m^p \<le> n then root_aux p n m h
        else root_aux p n l m
    )"  
    by pat_completeness auto
  termination 
    apply (relation "measure (\<lambda>(p,n,l,h). h-l)")
    apply simp_all
    done 
  
  lemmas [simp del] = root_aux.simps  

  lemma root_aux_correct: "l^p \<le> n \<Longrightarrow> n < h^p \<Longrightarrow> l<h 
    \<Longrightarrow> let r = root_aux p n l h in r^p\<le>n \<and> n<(r+1)^p"
    apply (induction n l h rule: root_aux.induct)
    apply (subst root_aux.simps)
    subgoal for n l h
      by (auto simp: Let_def dest: sqrt_aux_aux)
    
    done
  (*>*)

  (* Note: add special cases for 
    root p 0 = 0
    root p 1 = 1
    root 1 n = n
  *)  
  definition root :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
    (*<*)
    "root p n \<equiv> 
      if n=0 then 0 
      else if n=1 then 1 
      else if p=1 then n
      else root_aux p n 0 n"
    (*>*)

  (* The following lemmas will be helpful. 
    We'll see later how to find the proofs of many such lemmas automa{t,g}ically.
  *)    
  lemma root_aux1: "\<lbrakk>2\<le>p; 1<n\<rbrakk> \<Longrightarrow> n < n^p" for n :: nat 
    by (metis Suc_1 less_eq_Suc_le power_one_right power_strict_increasing_iff)
  
  lemma root_aux2: "1\<le>p \<Longrightarrow> Suc 0 < Suc (Suc 0) ^ p"
    by (metis One_nat_def lessI less_eq_Suc_le one_less_power)  
    
  thm zero_power  
    
    
  lemma root_correct: "1\<le>p \<Longrightarrow> let r = root p n in r^p\<le>n \<and> n < (r+1)^p"
  (*<*)
    unfolding root_def using root_aux_correct[of 0 p n n]
    by (auto simp: Let_def root_aux1 root_aux2 zero_power)
  (*>*)

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
  (*<*)
    apply (induction p y x rule: root_upper_bound_aux.induct)
    apply (subst root_upper_bound_aux.simps)
    apply auto
    done
  (*>*)  

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
    (*<*)  
    apply (induction p y x rule: root_upper_bound_aux.induct)
    subgoal for p y x
      apply (subst root_upper_bound_aux.simps)
      apply clarsimp
      apply (cases "2 ^ p * x ^ p \<le> y")
      apply simp
      apply (subst root_upper_bound_aux.simps)
      apply (simp)
      done      
    done    
    (*>*)

  (* For better readability of the goals, we define a function that fixes the
    start value. *)      
  definition "root_upper_bound p y \<equiv> root_upper_bound_aux p y 1"  
  
  (* Proof that it computes a valid bound. 
  
    unfold the definition of root_upper_bound, and use what you have already proved.
  *)
      
  lemma root_upper_bound1: "1\<le>p \<Longrightarrow> y < (root_upper_bound p y) ^ p"
    (*<*)
    unfolding root_upper_bound_def
    by (simp add: root_upper_bound_aux1)
    (*>*)
  
  lemma root_upper_bound2: "\<lbrakk>1\<le>p; 0<y\<rbrakk> \<Longrightarrow> (root_upper_bound p y div 2) ^ p \<le> y"
    (*<*)
    unfolding root_upper_bound_def
    apply (simp add: root_upper_bound_aux2)
    done
    (*>*)

  (* Finally define the root function again. 
    This time, use the more precise upper and lower bounds.
    Also add a special case for root p 0 = 0 
  *)    
  definition root' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  (*<*)
  "root' p y \<equiv> 
    if y=0 then 0 
    else 
      let
        h = root_upper_bound p y;
        l = h div 2
      in
        root_aux p y l h
    "
  (*>*)

  (*<*)
  lemma root_upper_bound_aux_pos: "0<x \<Longrightarrow> 0<root_upper_bound_aux p y x"
    apply (induction p y x rule: root_upper_bound_aux.induct)
    apply (subst root_upper_bound_aux.simps)
    by auto   
    
  lemma root_upper_bound_pos: "0<root_upper_bound p n"  
    unfolding root_upper_bound_def
    by (simp add: root_upper_bound_aux_pos)
  (*>*)  
    

  (* Prove your function correct. 
  
    You will need an auxiliary lemma that 0<root_upper_bound p n. 
    Prove a corresponding lemma for root_upper_bound_aux first.
  *)    
  lemma root'_correct: "1\<le>p \<Longrightarrow> let r = root' p n in r^p\<le>n \<and> n < (r+1)^p"
  (*<*)
    unfolding root'_def 
    using root_aux_correct[of "root_upper_bound p n div 2" p n "root_upper_bound p n"]
    using root_upper_bound1[of p n]
    using root_upper_bound2[of p n]
    by (auto simp add: Let_def root_upper_bound_pos)
  (*>*)  

  (* Now, you should be able to quickly compute roots, e.g. what is the 
    623rd root (rounded down) of 2^3370?
  *)
  (*<*)    
  value "root' 623 (2^3370)"
  
  value "root' 400 (6^400)"
  value "root' 600 (7^600)"
  (*>*)    
  
  
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
