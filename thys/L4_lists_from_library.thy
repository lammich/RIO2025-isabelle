section \<open>Lists in Isabelle's Library\<close>
theory L4_lists_from_library
imports Main "HOL-Library.Code_Target_Nat"
begin

  (* Lists provided by library *)
  typ "'a list"
  
  term Nil 
  term Cons 
  term append 
  
  (* Some fancy syntax *)
  term "[]"
  term "x#xs"
  
  term "1#2#3#4#[]"
  term "[1,2,3,4]"
  
  term "xs@ys"
  
  term rev 
  term concat 
  term length 
  term sum_list 
  term map 
  term set 
  term min_list 
  term fold 
  term foldr


  (* And many more functions *)  
                        

  subsection \<open>Sorting\<close>
  
  (*
    When is a sorting algorithm correct?
  *)

  (*<*)
  (*
    The result list is sorted. And contains exactly the elements of the original list!
  *) 
  (*>*) 
  
  (* Sortedness already exists in the library: *)
  term sorted
  

  subsubsection \<open>Element count\<close>
    
  
  (* We define the element count *)
  fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  (*<*)
    "count [] e = 0"
  | "count (x#xs) e = (if e=x then 1 + count xs e else count xs e)"  
  (*>*)

  (*<*)
  lemma count_append[simp]: "count (xs@ys) e = count xs e + count ys e"
    by (induction xs) auto
  (*>*)  
  
  (*<*)
  lemma in_set_count_iff: "x\<in>set xs \<longleftrightarrow> count xs x \<noteq> 0"
    by (induction xs) auto
  (*>*)  
    
  (* Let's show that equal element counts imply equal sets. *)
  lemma count_eq_imp_set_eq: "count xs = count ys \<Longrightarrow> set xs = set ys"
  (* Note the higher-order equality. Two functions being equal means they are equal for all arguments. *)
  thm fun_eq_iff
  (*<*)
    apply auto
    by (auto simp: in_set_count_iff)  
  (*>*)  

  
  subsubsection \<open>Quicksort\<close>
  
  (*
    Idea of quicksort: 
      \<^item> pick a pivot element p
      \<^item> partition the remaining elements into \<le>p and >p
      \<^item> recursively sort the partitions, and apppend
  
    Simple version: pick first element of list as pivot  
      
  *)
      

  fun quicksort :: "nat list \<Rightarrow> nat list" where    
  (*<*)
    "quicksort [] = []"
  | "quicksort (p#xs) = quicksort (filter (\<lambda>x. x\<le>p) xs) @ p # quicksort (filter (\<lambda>x. p<x) xs)"  
  (*>*)

  (*<*)
  lemma count_filter_aux: "count (filter (\<lambda>x. x\<le>p) xs) x + count (filter (\<lambda>x. p<x) xs) x = count xs x" for xs::"nat list" 
    by (induction xs) auto
  
  lemma count_quicksort[simp]: "count (quicksort xs) = count xs"
    apply (induction xs rule: quicksort.induct)
    apply (auto simp: fun_eq_iff count_filter_aux)
    done

  lemmas set_quicksort[simp] = count_eq_imp_set_eq[OF count_quicksort]  
  (*>*)    
      
  lemma sorted_quicksort[simp]: "sorted (quicksort xs)"
  (* We'll get stuck here on first attempt. Do count first, and derive set= from that! *)
  (*<*)
    apply (induction xs rule: quicksort.induct)
    apply (auto simp: sorted_append)
    done
  (*>*)  
  

  
  
  
  
  
  subsection \<open>Prime Factorization (advanced Isabelle)\<close>
  
  (*
    Let's do something slightly more complicated: trial division to find the prime factorization
    of a number. 
    While this algorithm is not super-complicated, it already requires to combine
    some mathematics with the correctness reasoning about the algorithm.
    This is the domain of interactive theorem provers, where we have detailed control over the proof,
    and can split it into small pieces, far beyond what fully automatic provers can do.  
    
    And, for the 'easy' parts, Isabelle even provides a very powerful automated theorem prover,
    which is also trustworthy, as the proofs that it produces are replayed in Isabelle's kernel.
  *)  
  
  (*
    Let's start with the trial division algorithm:
    
    We successively try to divide our number by increasing divisors, starting at 2.
    Whenever we can divide, we add the divisor to the result list. 
    
    Example: n=45
      Test for increasing k:
      
      k=2: -
      k=3: add 3, remaining 15
      k=3: add 3, remaining 5
      Now, k\<^sup>2>5, thus 5 is the last prime
      
      Factorization: [3,3,5]
      
    
    Before we see why this algorithm works, let's write it down in Isabelle.
    For that, we need to see why it terminates:
      A simple argument is as follows: we terminate when k\<^sup>2>n, 
      and either decrease n or increase k. Thus n + 1 - k\<^sup>2 will get smaller in every recursion.   
    
  *)  
      
  function pf_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
    "pf_aux k n = (
      if k\<^sup>2>n \<or> k<2 \<or> n=0 then [n] 
      else if k dvd n then k # pf_aux k (n div k) 
      else pf_aux (k+1) n)"
    by pat_completeness auto
  termination 
    apply (relation "measure (\<lambda>(k,n). n + 1 - k\<^sup>2)")
    (*<*)
    subgoal by simp
    subgoal 
      by clarsimp (metis One_nat_def diff_less_mono div_less_dividend less_Suc0 nat_less_le not_less_eq numeral_2_eq_2 zero_less_diff)
    subgoal 
      by (simp add: diff_less_mono2 power_strict_mono)
    done
    (*>*)
    
  (*
    To find the proofs, we have used the sledgehammer tool.
    
    Sledgehammer sends the proof goal and some relevant facts (determined by a heuristics) to
    a suite of automated theorem provers (CVC4, Z3, Vampire, etc). When a proof is found,
    it tries to reconstruct the proof in Isabelle's kernel.
    Thus, Isabelle's TCB is not compromised, but we can use the power of ATPs.
    
    In practice, sledgehammer is the single most useful Isabelle tool for advanced users.
    For beginners, it is a little dangerous, as it finds many simple proofs without requiring 
    an understanding of what is happening. However, understanding is necessary to advance 
    to more complicated proofs beyond sledgehammers capabilities.
    
    Also note that, after exploring the proof, we have cleaned it up a bit. 
    The goal was to make it more robust. In particular, you do not want any parts of the proof
    depending on a preceeding auto. Ideally, only simple methods (rule, intro) are used in non-final
    position. 
    
    Reason: the more complex the proof method, the more likely it's result is to change in the next
      Isabelle version, and break the whole proof structure that comes after it. 
    
  *)
    
  lemmas [simp del] = pf_aux.simps  

  value "pf_aux 2 45"

  (* It's relatively straightforward to show that pf_aux returns a sorted factorization 
    of the input number. *)
      
  lemma pf_aux_factorization: "prod_list (pf_aux k n) = n"
    apply (induction k n rule: pf_aux.induct)
    apply (subst pf_aux.simps)
    by auto
  
  lemma in_set_pf_auxD: "p\<in>set (pf_aux k n) \<Longrightarrow> k\<le>p \<or> p=n"  
    apply (induction k n rule: pf_aux.induct)
    apply (subst (asm) pf_aux.simps)
    apply (auto split: if_splits simp: less_eq_div_iff_mult_less_eq power2_eq_square) 
    done
    
  lemma pf_aux_sorted: "sorted (pf_aux k n)"
    apply (induction k n rule: pf_aux.induct)
    apply (subst pf_aux.simps)
    apply (auto simp: less_eq_div_iff_mult_less_eq numeral_2_eq_2 dest: in_set_pf_auxD) 
    done

  (* It remains to show that all elements returned by pf_aux are prime. 
    We first define prime numbers: *)  

  (* A number is prime, if it is >1 and can only be divided by 1 and itself *)
  definition prime :: "nat \<Rightarrow> bool" 
    where "prime p \<equiv> p>1 \<and> (\<forall>u\<in>{2..<p}. \<not> u dvd p)"    

  (* Note: we have cheated and added a <p, rather than \<noteq>p. Fortunately, that's equivalent *)
  lemma "prime p \<longleftrightarrow> p>1 \<and> (\<forall>u. u\<notin>{1,p} \<longrightarrow> \<not> u dvd p)"
    (* Explore, sledgehammer, clean up *)
    (*<*)
    unfolding prime_def
    apply (intro iffI) 
    subgoal
      apply clarsimp
      by (metis atLeastLessThan_iff bot_nat_0.extremum dvd_imp_le dvd_pos_nat less_2_cases_iff linorder_not_le nat_less_le)
    subgoal by auto
    done
    (*>*)

    
  (* We follow the proof in a nice book by Gert Smolka (in German). 
     Programmierung – eine Einführung in die Informatik mit Standard ML, chapter 5.8
     2008 Oldenbourg Wissenschaftsverlag GmbH
     ISBN 978-3-486-58601-5     
  
     (You'll find pdf's on Google)   
     
     
     We first define a precondition for application of the function:
     
     We only apply pf_aux k n when 2\<le>k\<le>n, and n is not divisible by any number 2..<k.
  *)  
  definition pf_aux_pre :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
    where "pf_aux_pre k n \<equiv> 2\<le>k \<and> k\<le>n \<and> (\<forall>u\<in>{2..<k}. \<not> u dvd n)"

    
  (*
    We now have to show that:
    
    pf_aux_pre holds initially, i.e., for k=2
  
    pf_aux_pre is preserved for recursive calls, and when a number is added to the list,
      it implies that this is a prime number
      
    When the algorithm terminates, k\<^sup>2>n, then n is a prime number.  
  *)  
    
  lemma pf_aux_pre_init: "2\<le>n \<Longrightarrow> pf_aux_pre 2 n"
    unfolding pf_aux_pre_def by simp  

    
  (* We show the termination case first *)      
          
  lemma "pf_aux_pre k n \<Longrightarrow> k\<^sup>2>n \<Longrightarrow> prime n"
    unfolding pf_aux_pre_def power2_eq_square prime_def
    apply auto
    (* sledgehammer -- no proof found *)
    oops      

  (* That's getting a bit too complicated. Time to introduce a more powerful proof language. 
  
    Let's sketch out the proof on paper first:

    
    We have to show 
      1<n and \<forall>u\<in>{2..<n}. \<not>u dvd n
      
    The first part is trivial from pf_aux_pre.  
      
    For the second part, we assume there is an u with 2\<le>u<n, such that u dvd n, and show a contradiction
    
    As u dvd n, there is a v with n = u*v. That is also v dvd n.
    As 2\<le>u<n, also 2\<le>v<n.
    
    Because of pf_aux_pre, we know that u,v\<ge>k
    Hence k\<^sup>2 \<le> u*v
    
    Thus n = u*v \<ge> k\<^sup>2 > n. Contradiction. qed
  *)  
    
  lemma pf_aux_pre_term_imp_post:
    assumes PRE: "pf_aux_pre k n"
    assumes "k\<^sup>2>n"
    (*shows "\<forall>u\<in>{2..<n}. \<not>u dvd n"*)
    shows "prime n"
    unfolding prime_def
  proof 
    from PRE show "1<n" unfolding pf_aux_pre_def by simp
  
    show "\<forall>u\<in>{2..<n}. \<not> u dvd n"  
    proof clarsimp (* Do the 'obvious' initial steps *)
      fix u
      assume "2\<le>u" "u<n" "u dvd n"
      
      from \<open>u dvd n\<close> obtain v where N: "n = u*v" and \<open>v dvd n\<close> by auto
      with \<open>2\<le>u\<close> \<open>u<n\<close> have "2\<le>v" "v<n" by auto
      
      have "k\<le>u" "k\<le>v" 
        using PRE \<open>2\<le>u\<close> \<open>2\<le>v\<close> \<open>u dvd n\<close> \<open>v dvd n\<close> 
        unfolding pf_aux_pre_def by auto
      have "k\<^sup>2\<le>u*v" 
        unfolding power2_eq_square 
        using mult_mono[OF \<open>k\<le>u\<close> \<open>k\<le>v\<close>] 
        using \<open>2\<le>u\<close> \<open>2\<le>v\<close> 
        by simp
      
      note \<open>n<k\<^sup>2\<close> also note \<open>k\<^sup>2 \<le> u*v\<close> also note \<open>n = u*v\<close>[symmetric] 
      finally show False by simp 
    qed  
  qed    

  (*
    Note that this proof follows our paper proof sketch very closely.
    The Isar proof language is designed to express proofs in a human readable form,
    and resemble what you would write on paper.
    
    Actually, when proofs get more complicated, you'll need to sketch out the proof on paper before
    starting to formalize it. Also, the more experienced you are 
    (both in Isabelle and in the domain of the proof), the less sketches you will need.
  *)
  
  

  (*
    The next two proofs cover the recursion cases.
    
    For the first proof, I have started with an Isar proof (and no proof sketch),
    and used sledgehammer to shortcut the first goal. 
    You may realize that it is rougher than the above, elaborated proof.
    
    Here, theorem proving meets software engineering, and we can have hacky proofs and clean proofs.
    However, all proofs go through Isabelle's kernel, so they are correct. The difference is in
    maintainability, readablity, etc.
  *)  
      
  lemma pf_aux_dvd: 
    assumes PRE: "pf_aux_pre k n" 
    assumes A: "k\<^sup>2\<le>n" "k dvd n" 
    shows "prime k" "pf_aux_pre k (n div k)"
  proof -
  
    from PRE A(1) have "2\<le>k" "k<n"
      unfolding pf_aux_pre_def
      by (auto simp: power2_eq_square simp flip: linorder_not_le) 

    show "prime k"
      unfolding prime_def using \<open>2\<le>k\<close>
      apply clarsimp
      by (meson PRE assms(3) atLeastLessThan_iff dvd_trans pf_aux_pre_def)
      
        
    from A(2) obtain k' where N: "n = k*k'" and K': "k' dvd n" by auto
    with \<open>2\<le>k\<close> \<open>k<n\<close> have "2\<le>k'" "k'<n" by auto
      
    with PRE K' have "k\<le>k'"
      unfolding pf_aux_pre_def
      by auto
      
    from PRE show "pf_aux_pre k (n div k)"
      unfolding pf_aux_pre_def
      by (auto simp: N \<open>k\<le>k'\<close>) 
      
  qed
      
  (* The last case went by sledgehammer *)    
  lemma pf_aux_ndvd: 
    assumes "pf_aux_pre k n" "k\<^sup>2\<le>n" "\<not>k dvd n" 
    shows "pf_aux_pre (k+1) n"
    using assms unfolding pf_aux_pre_def
    apply (intro conjI)
    subgoal by simp
    subgoal
      by simp (metis dvd_triv_left less_eq_Suc_le nat_less_le nat_mult_1_right)
    subgoal
      by simp (metis atLeastLessThan_iff nat_neq_iff not_less_eq)
    done  
  
  
  (* Now we can show the desired theorem *)
  lemma pf_aux_primes: "pf_aux_pre k n \<Longrightarrow> x\<in>set (pf_aux k n) \<Longrightarrow> prime x"  
    apply (induction k n rule: pf_aux.induct)
    apply (subst (asm) pf_aux.simps) 
    apply (clarsimp split: if_splits)
    subgoal for k
      apply safe apply (simp_all add: pf_aux_pre_term_imp_post)
      unfolding pf_aux_pre_def by auto
    subgoal for k n
      using pf_aux_dvd by auto
    subgoal for k n
      using pf_aux_ndvd by auto
    done        
        

  (* Finally, we wrap pf_aux into a function that starts with k=2, and prove that correct using the
    above lemmas *)    
    
  definition "pf n = (if n<2 then [n] else pf_aux 2 n)"
    
  lemma pf_correct:
    "prod_list (pf n) = n"
    "sorted (pf n)"
    "2\<le>n \<Longrightarrow> p\<in>set (pf n) \<Longrightarrow> prime p"
    unfolding pf_def
    subgoal
      using pf_aux_factorization by auto
    subgoal
      using pf_aux_sorted by auto
    subgoal 
      using pf_aux_primes[of 2 n p] 
        (* Sometimes instantiating a lemma reduces the search space, and enables an easy proof *)
      by (auto simp: pf_aux_pre_init)     
    done  
    
  value "pf 76"

  value "pf 7836872"
  
  
  

end
