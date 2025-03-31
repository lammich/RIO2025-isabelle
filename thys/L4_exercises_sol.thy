section \<open>L4 Exercises\<close>
theory L4_exercises
imports L4_lists_from_library
begin

  subsection \<open>Mergesort\<close>

  (* 
    The idea of mergesort is to split the list in half, recursively sort the two halfs,
    and then merge the two halfs to one sorted list. 
  *)
  
  (*
    Merging two sorted lists into one sorted list can be done by only looking at the first
    elements of the two lists, selecting the smaller one.
    
    Implement merge, and show that it preserves the element count, and, if both lists are sorted,
    yields a sorted list.
  *)
  
  
  fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
    "merge [] ys = ys"
  | "merge xs [] = xs"
  (* add the missing equation *)
  (*<*)
  | "merge (x#xs) (y#ys) = (if x\<le>y then x # merge xs (y#ys) else y # merge (x#xs) ys)"    
  (*>*)

  (* Show that merge preserves the element count. *)    
  lemma count_merge[simp]: "count (merge xs ys) = count (xs@ys)"
  (*<*)
    apply (induction xs ys rule: merge.induct)
    by auto
  (*>*)  

  (* Note that we have stated the above lemma slightly strangely. Instead of
    \<lambda>e. count xs e + count ys e, we used count (xs@ys).
    The only reason we did that is to be able to use count_eq_imp_set_eq, which expects
    a top-level count:
  *)
  lemmas set_merge[simp] = count_eq_imp_set_eq[OF count_merge]   

  (* Show that two sorted lists are merged into a sorted list *)    
  lemma sorted_merge: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge xs ys)"  
    (*<*)
    by (induction xs ys rule: merge.induct) auto
    (*>*)

  (* We have implemented mergesort for you. take and drop take/drop the first elements of a list *)      
  fun mergesort :: "nat list \<Rightarrow> nat list" where
    "mergesort [] = []"
  | "mergesort [x] = [x]"
  | "mergesort xs = (let m = length xs div 2 in merge (mergesort (take m xs)) (mergesort (drop m xs)))"  

  
  (* The following auxiliary lemma may come in handy! 
  
    This lemma is a bit tricky to prove, as the simplifier plays against us.
    So let's go back to the basics!
    
    To prove this lemma, you first need to rewrite
    
      xs = take m xs @ drop m xs
    
    but only on the right hand side of the equation. 
    You can use subst (i) \<dots> to select the ith occurence for rewriting.
    Note that the simplifier cannt do that, as it would rewrite all occurences of xs, 
    recursively and infinitely often.
      
    Then, you need to rewrite with count_append, to make the left and right hand side equal.
  *)    
  lemma count_split_aux: "count (take m xs) e + count (drop m xs) e = count xs e"
    (* Use this lemma for the first subst. The symmetric flips the equation, 
      and the instantiation to xs reduces the possible matches. Otherwise it would match 
      any list subterm in the statement, and you'd need a larger (i) with subst. *)
    thm append_take_drop_id[symmetric, of xs] 

    (* Then use subst and rule with the following lemmas, to finish the proof *)    
    thm count_append refl
    (*<*)  
    apply (subst (3) append_take_drop_id[symmetric, of xs])
    apply (subst count_append)
    apply (rule refl)
    done
    (*>*)

  (* Now that you have got a bit more practice in Isabelle low-level reasoning, note that there
    is another way to prove the lemma: 
    
    first rewrite the lhs with count_append[symmetric] to get
    
      count (take m xs @ drop m xs) e = \<dots>
    
    then simplify take m xs @ drop m xs = xs  (this lemma, append_take_drop_id, is in the simpset)
    and finish by reflexivity.
    
    Here, we have used count_append the other way round. As this occurs very often, the simplifier
    has a shortcut to add the symmetric version of a lemma 
    (and remove the original should it be in the simpset)
    *)  
    
  lemma "count (take m xs) e + count (drop m xs) e = count xs e"
    by (simp flip: count_append)
    
      
  (* Prove mergesort correct*)  
  lemma count_mergesort: "count (mergesort xs) = count xs"
  (*<*)
    apply (induction xs rule: mergesort.induct)
    apply (auto simp: fun_eq_iff count_split_aux)    
    done
  (*>*)
          
  lemmas set_mergesort[simp] = count_eq_imp_set_eq[OF count_mergesort]   
    
  lemma sorted_mergesort: "sorted (mergesort xs)"
  (*<*)
    apply (induction xs rule: mergesort.induct)
    apply (auto simp: sorted_merge)
    done
  (*>*)
    





end
