section \<open>L3 Exercises\<close>
theory L3_exercises
imports L3_lists_from_basics
begin
  (* These exercises are to be solved with the toy list 
    datatype definition from the first list lecture.
    
    Nevertheless, for readability, we'll use [...] syntax for lists in the text.
  *)

  subsection \<open>Concat\<close>
  
  (* Define a function concat that flattens a list of lists. 
  
    E.g. concat [ [1,2],[3],[],[4,5,6] ] = [1,2,3,4,5,6]
  *)

  fun concat :: "'a list list \<Rightarrow> 'a list" where
  
  
  value "concat (Cons (Cons 1 (Cons 2 Nil)) (Cons Nil (Cons (Cons 3 (Cons 4 Nil)) Nil))) :: nat list"
  
  (* State and show the append lemma for concat: concat (append xs ys) = \<dots> *)
  
  lemma concat_append[simp]:   


  (* If you reverse the inner lists, and then reverse the outer list, and then concat,
    you could as well concat and then reverse the result. Prove that.
  *)
  lemma "concat (rev (map rev xss)) = rev (concat xss)"
    

  (* Show that an element is in the flattened list, iff it is in at least one of the inner lists *)  
  lemma "x\<in>set (concat xss) \<longleftrightarrow> (\<exists>xs\<in>set xss. x\<in>set xs)" 
    
  
  
  
  subsection \<open>Length\<close>
  
  (* Define a function that returns the length of a list *)
  fun length :: "'a list \<Rightarrow> nat" where
  

    

  (* Show: mapping a list preserves its length *)  
  lemma length_map[simp]: "length (map f xs) = length xs"    
    by (induction xs) auto
    
  (* Show: reversing a list preserves its length.
  
    Hint: maybe you need an append lemma for length first
  *)
  lemma length_rev[simp]: "length (rev xs) = length xs"  
      

  
  (* Show: the length of a list is zero, iff the list is empty *)      
  lemma length_zero: "length xs = 0 \<longleftrightarrow> xs=Nil"    
  

    
    
    
    
  (* Show: the length of a concatenated list is the sum of the lengths of the inner lists *)  
  lemma "length (concat xss) = list_sum (map length xss)"
  

  (* Find a suitable precondition for when the length of a list is \<le> the sum of its elements: *)    
  lemma "xxx \<Longrightarrow> length xs \<le> list_sum xs" oops
    

  subsection \<open>Exercise: a lot via fold\<close>    
  
  (* Express the following functions as folds, and prove the statement.
  
    Hint: you'll need to prove an auxiliary lemma first, that generalizes over the accumulator
  *)
  
  lemma "rev xs = fold x y z" oops
  
  lemma "length xs = fold x y z" oops
  
  
    

    

  (* The product of the elements in a list can be written with fold.
    Show that the product is 0 iff the list contains a zero.
  *)  
  lemma fold_times_zero_iff_nat: "fold (*) xs 1 = 0 \<longleftrightarrow> 0\<in>set xs" for xs :: "nat list"
  

  
  subsubsection \<open>Type-classes (advanced) \<close>  
  (* In the last lemma, not the explicit type constraint \<open>for xs :: "nat list"\<close>. 
    Without that type constraint, xs would be inferred to have type 'a list,
    for 'a being any type that defines multiplication, 0, and 1. 
    However, no laws are required. In particular, we don't know if x*0 = 0. 
    Thus, the statement does not hold in that generality.
  *)      

  context
    notes [[show_sorts]]  (* Enable display of types and sorts (type classes) for this context only *)
  begin
    term "fold (*) xs 1 = 0"  

    find_theorems "_*0=0" (* Let's find a type class where this x*0=0 *)
      
    find_theorems "_*_=0" "_=0 \<or> _=0" (* 
      Also, we should have no zero divisors, i.e., the only way to produce 0 is by multiplying with zero *)
      
    print_classes    
    class_deps semiring (* See the output window for a link to the class graph *)
      
    (* As we also need a one, semiring_1_no_zero_divisors seems to be a reasonable pick *)
  
  end

    
  
  lemma fold_times_zero_iff: "fold (*) xs 1 = 0 \<longleftrightarrow> 0\<in>set xs"
    for xs :: "'a::semiring_1_no_zero_divisors list"
    
  

    

  subsection \<open>fold-right\<close>

  (* 
    Note the order in which fold iterates over the list:
      fold f [a,b,c] s = f c (f b (f a s))
  
    that is, the first element of the list is processed first 
      (note that function application notation is right to left, 
        thus the order appears backwards here)  
        

    Implement a function foldr that processes the last element of the list first:    
      foldr f [a,b,c] s = f a (f b (f c s))
  
  *)
  

  fun foldr :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's" where
  

  (* Check that you get the expected values *)
  value "fold f (Cons a (Cons b (Cons c Nil))) s"
  value "foldr f (Cons a (Cons b (Cons c Nil))) s"
  
  (* State and prove an append lemma for foldr *)  
      
  lemma foldr_append[simp]:   

  (* Show that folding with Cons is the identity operation *)  
  lemma foldr_Cons_id: "foldr Cons xs Nil = xs"  
    
    
  (* Express map with foldr. map f xs = foldr \<dots> *)
  lemma "map f xs = foldr x y z" oops    
  
    

  (* Express concat with foldr *)
  lemma "concat xss = foldr x y z" oops
      
    
    
  (* State fold in terms of foldr *)
  lemma "fold f xs s = foldr x y z" oops
  
  
    
  
  
  
  

end
