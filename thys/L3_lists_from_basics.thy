section \<open>L3: Lists from Basic Principles\<close>
theory L3_lists_from_basics
imports Main
begin


  hide_const Nil Cons append rev concat length sum_list map set min_list fold foldr

  hide_type list

  
  subsection \<open>List Datatype\<close>

  (*
    A list is construted by prepending elements to the empty list
  *)
  datatype 'a list = Nil | Cons 'a "'a list"

  typ "nat list"
  typ "bool list"
  
  term "Cons (0::nat) (Cons 2 (Cons 5 Nil))"
  term "Cons True (Cons False (Cons True Nil))"
  
  (* Note: this can be seen as a generalization of nat, cf *)
  term "Suc (Suc (Suc 0))"
  

  subsection \<open>Append\<close>
  
  fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "append Nil ys = ys"
  | "append (Cons x xs) ys = Cons x (append xs ys)"  

  (* cf with 
    0+b = b
    Suc a + b = Suc (a+b) 
  *)
  
  (* Nil is right-neutral element *)    
  lemma append_right_Nil[simp]: "append xs Nil = xs"
    by (induction xs) auto

  (* Append is associative *)    
  lemma append_assoc[simp]: "append (append xs ys) zs = append xs (append ys zs)"  
    by (induction xs) auto
  
  (* Note: contrary to +, append is not commutative! *)  
    

  subsection \<open>Reverse\<close>
        
  fun rev :: "'a list \<Rightarrow> 'a list" where
    (*<*)
    "rev Nil = Nil"
  | "rev (Cons x xs) = append (rev xs) (Cons x Nil)"    
    (*>*)
    
  (*<*)
  (* Auxiliary lemma needed for rev_rev! *)
  lemma rev_append[simp]: "rev (append xs ys) = append (rev ys) (rev xs)"
    by (induction xs) auto
  (*>*)

  (* Reversing twice yields original list *)  
  lemma rev_rev[simp]: "rev (rev xs) = xs"
  (*<*)
    apply (induction xs)
    apply auto
    done  
  (*>*)

  (* Note: append-lemmas, that distribute append over other functions, are very useful and you
    typically prove them for any list-function where they make sense!
    In most cases, they are good [simp]-lemmas. 
  *)  

  
  subsection \<open>Map\<close>
  (* Apply a function to each element of a list. 
  
    map f [a,b,c,\<dots>] = [f a, f b, f c, \<dots> ]
  *)    
  
  fun map :: "('a\<Rightarrow>'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  (*<*)
    "map f Nil = Nil"
  | "map f (Cons x xs) = Cons (f x) (map f xs)"    
  (*>*)
    
  lemma map_append[simp]: "map f (append xs ys) = append (map f xs) (map f ys)"
  (*<*)
    by (induction xs) auto
  (*>*)  
  
  
  subsection \<open>Sum up elements in list\<close>    
    
    
  fun list_sum :: "nat list \<Rightarrow> nat" where
  (*<*)
    "list_sum Nil = 0"
  | "list_sum (Cons x xs) = x + list_sum xs"    
  (*>*)  

  lemma list_sum_append[simp]: (*<*)"list_sum (append xs ys) = list_sum xs + list_sum ys"    
    by (induction xs) auto
  (*>*)  

    
    
  subsection \<open>Fold\<close>    
    
  (*
    Iterate over elements of list. 
    
    fold f [a,b,c] s = f c (f b (f a s))
  *)
          
  fun fold :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's" where
  (*<*)
    "fold f Nil s = s"
  | "fold f (Cons x xs) s = fold f xs (f x s)"    
  (*>*)
    
  value "fold f (Cons a (Cons b (Cons c Nil))) s"
  
  lemma fold_append[simp]: (*<*)"fold f (append xs ys) s = fold f ys (fold f xs s)"  
    apply (induction xs arbitrary: s)
    by auto
  (*>*)  

  (* fold can be used to elegantly express many functions on lists *)
      
  lemma "list_sum xs = fold (+) xs 0"
  (*<*)
    apply (induction xs) 
    apply auto
  (*>*)  
    oops

  (* During the fold, the value of the accumulator (s) changes. 
    Thus, we have to generalize the lemma accordingly: 
  *)  
  
  (*<*)      
  lemma list_sum_fold_aux: "fold (+) xs a = list_sum xs + a"
    apply (induction xs arbitrary: a) 
    by auto  
  (*>*) 

  (* Then use the generalized aux-lemma to prove the original statement *)  
  lemma "list_sum xs = fold (+) xs 0"    
  (*<*)      
    by (simp add: list_sum_fold_aux)  
  (*>*) 
    

  subsection \<open>Set of Elements in List\<close>
    
  fun set :: "'a list \<Rightarrow> 'a set" where
    "set Nil = {}"
  | "set (Cons x xs) = insert x (set xs)"    

  (*
    Isabelle's 'a set type represents a set.
  *)
  typ "'a set"
  term insert (* Insert single element *)
  (* standard set operations. *)
  term "a \<union> b"
  term "a \<inter> b"
  term "a - b"
  term "x\<in>s"
  
  (* Note: type and constant name-spaces are different. 
    Thus, the function set :: 'a list \<Rightarrow> 'a set, and the type 'a set do not clash.
  *)

  lemma set_append[simp]: 
  (*<*)
    "set (append xs ys) = set xs \<union> set ys"  
    by (induction xs) auto
  (*>*)
    
  (* Inversion lemma: the set of elements is empty, iff the list is empty *)  
  lemma set_empty: "set xs = {} \<longleftrightarrow> xs=Nil"
  (*<*)
    by (cases xs) auto
  (*>*)  
  (* Note: while this lemma can be proved by induction, an induction proof is overkill here: 
    a simple case distinction on xs is enough. *)
  
  
  

  subsection \<open>Maximum element in List\<close>  
  
  fun max_list :: "nat list \<Rightarrow> nat" where
  (*<*)
    "max_list Nil = 0"  
  | "max_list (Cons x xs) = max x (max_list xs)"  
  (*>*)

  (* Show that every element in the list is \<le> the mximum element *)
  lemma "x\<in>set xs \<Longrightarrow> x\<le>max_list xs"
  (*<*)
    by (induction xs) auto
  (*>*)  
  
  (* Let's show that the maximum element is contained in the list (unless the list is empty)*)      
  lemma "xs\<noteq>Nil \<Longrightarrow> max_list xs \<in> set xs"
  (* We'll require some extra case distinction in the proof *)
  (*<*)
    apply (induction xs)
    apply simp
    subgoal for x xs
      (* Note: sometimes, extra case distinctions are hard to avoid. *)
      apply (cases xs)
      by auto
    done  
  (*>*)  
    

end
