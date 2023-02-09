theory BC_Logic
  imports Main 

begin
section \<open>message, bool and their evaluation\<close>

datatype msg = EMPTY | ITE bl msg msg | Cons msg msg | ATOM string 
and bl = EQ msg msg | EQL msg msg | T | F

function (sequential) eval :: "msg => string" and bval :: "bl => bool" where
"eval m = (
  case m of EMPTY => ([]::string) |
  (Cons s m) => eval s @ eval m|
  (ITE b m1 m2) => (
    if bval b then eval m1 else eval m2
  ) |
  (ATOM s) => s
)" |
"bval b = (
  case b of T => True |
  F => False |
  (EQ m1 m2) => if eval m1 = eval m2 then True else False |
  (EQL m1 m2) => if length (eval m1) = length (eval m2) then True else False
)" by pat_completeness auto
termination by lexicographic_order

section \<open>complexity analysis\<close>

function (sequential) T_eval :: "msg => nat" and T_bval :: "bl => nat" where
"T_eval m = (
  case m of 
  EMPTY \<Rightarrow> 0 |
  (Cons s m) \<Rightarrow> T_eval s + T_eval m + 1|
  (ITE b m1 m2) \<Rightarrow> (
    T_bval b + (if bval b then T_eval m1 else T_eval m2) + 1
  ) |
  (ATOM s) \<Rightarrow> length s
)" |
"T_bval b = (
  case b of T \<Rightarrow> 0 |
  F \<Rightarrow> 0 |
  (EQ m1 m2) \<Rightarrow> 1 + T_eval m1 + T_eval m2 |
  (EQL m1 m2) \<Rightarrow> 1 + T_eval m1 + T_eval m2
)" by pat_completeness auto
termination by lexicographic_order

function (sequential) msg_len :: "msg => nat" and bl_len :: "bl => nat" where
"msg_len m = (
  case m of EMPTY => 1 |
  (Cons s m) => msg_len s + msg_len m + 1|
  (ITE b m1 m2) => (
    bl_len b + msg_len m1 + msg_len m2 + 1
  ) |
  (ATOM s) => length s
)" |
"bl_len b = (
  case b of T => 1 |
  F => 1 |
  (EQ m1 m2) => 1 + msg_len m1 + msg_len m2 |
  (EQL m1 m2) => 1 + msg_len m1 + msg_len m2 
)" by pat_completeness auto
termination by lexicographic_order

(*to guarantee the linear complexity, we have to double the length of bl in ITE
technically this means a doubled buffer time for the verfication of the condition*)

theorem linear_eval: "T_eval msg \<le> msg_len msg" "T_bval bl \<le>  bl_len bl"
proof (induct msg and bl rule: msg_len_bl_len.induct) 
case (1 m)
  then show ?case 
  by (cases m) auto
next
  case (2 b)
  then show ?case
  by (cases b) auto
qed

theorem linear_complexity: 
"\<exists>a b. T_eval msg \<le> a * msg_len msg + b" 
"\<exists>a b. T_bval bl \<le> a * bl_len bl + b"
using linear_eval le_add2 by blast+

section \<open>abstract the protocol as tries\<close>

datatype  proc_trie = Rt "(bl \<times> proc_trie) list" | Nd msg "(bl \<times> proc_trie) list" 

fun is_nd :: "proc_trie => bool" where
"is_nd (Rt _) = False" | "is_nd (Nd _ _) = True"

fun valid :: "proc_trie => bool" where
"valid (Rt []) = True" |
"valid (Nd _ []) = True" |
"valid (Rt (x#l)) = (card (set (x#l)) = card (fst` (set (x#l))) \<and> 
  (\<forall>t\<in> (snd ` (set (x#l))). valid t \<and> is_nd t))" |
"valid (Nd _ (x#l)) = (card (set (x#l)) = card (fst` (set (x#l))) \<and> 
  (\<forall>t\<in> (snd ` (set (x#l))). valid t \<and> is_nd t))"

lemma valid_children_root: 
  assumes "valid (Rt (x # l))"
  shows "valid (snd x)" and "valid (Rt l)"
  using assms proof (induction l arbitrary: x) 
  case (Cons a l) 
   {
    case 2
    let ?s="(set (x # a # l))"
    let ?s'="set (a # l)"
    from 2 have "card ?s = card (fst ` ?s)"
      "\<forall>t \<in> (snd ` ?s). valid t \<and> is_nd t" by simp+
    moreover have "?s' \<subseteq> ?s" "fst ` ?s' \<subseteq> fst ` ?s" by fastforce+
    ultimately have "card ?s' = card (fst ` ?s')" "\<forall>t \<in> (snd ` ?s'). valid t \<and> is_nd t"
     by (metis List.finite_set card_image eq_card_imp_inj_on inj_on_insert list.simps(15), simp)
    then show ?case by simp
   }
  qed auto

lemma valid_children_node:
assumes "valid (Nd m (x # l))"
  shows "valid (snd x)" and "valid (Rt l)"
  using assms proof (induction l arbitrary: x) 
    case (Cons a l) 
   {
    case 2
    let ?s="(set (x # a # l))"
    let ?s'="set (a # l)"
    from 2 have "card ?s = card (fst ` ?s)"
      "\<forall>t \<in> (snd ` ?s). valid t \<and> is_nd t" by simp+
    moreover have "?s' \<subseteq> ?s" "fst ` ?s' \<subseteq> fst ` ?s" by fastforce+
    ultimately have "card ?s' = card (fst ` ?s')" "\<forall>t \<in> (snd ` ?s'). valid t \<and> is_nd t"
     by (metis List.finite_set card_image eq_card_imp_inj_on inj_on_insert list.simps(15), simp)
    then show ?case by simp
   }
  qed auto

fun sz :: "proc_trie => nat" where
"sz (Rt []) = 1" |
"sz (Rt (x#l)) = 1 + sz (snd x) + sz (Rt l) " |
"sz (Nd _ []) = 1" |
"sz (Nd _ (x#l)) = 1 + sz (snd x) + sz (Rt l)"

fun lf :: "proc_trie => nat" where
"lf (Rt []) = 1" |
"lf (Rt (x#l)) = lf (snd x) + lf (Rt l)" |
"lf (Nd _ []) = 1" |
"lf (Nd _ (x#l)) = lf (snd x) + lf (Rt l)"

fun nd :: "proc_trie => nat" where
"nd (Rt []) = 0" |
"nd (Rt (x#l)) = 1 + nd (snd x) + nd (Rt l)" |
"nd (Nd _ []) = 0" |
"nd (Nd _ (x#l)) = 1 + nd (snd x) + nd (Rt l)"

theorem nd_lf_sz_sound: "nd proc + lf proc = sz proc"
by (induction proc rule: sz.induct) auto

fun get_msg :: "proc_trie => msg" where
"get_msg (Rt []) = EMPTY" |
"get_msg (Nd m []) = m" |
"get_msg (Rt ((b, x) # xs)) = (
  if bval b then get_msg x else get_msg (Rt xs)
)" |
"get_msg (Nd m ((b, x) # xs)) = (
  if bval b then Cons m (get_msg x) else Cons m (get_msg (Rt xs))
)"

section \<open>fold the protocol to obtain one single rule given as single message\<close>

fun fold :: "proc_trie => msg" where
"fold (Rt []) = EMPTY" |
"fold (Nd m []) = m" |
"fold (Rt ((b, x) # xs)) = ITE b (fold x) (fold (Rt xs))" |
"fold (Nd m ((b, x) # xs)) = Cons m (ITE b (fold x) (fold (Rt xs)))"

fun T_fold :: "proc_trie => nat" where
"T_fold (Rt []) = 1" |
"T_fold  (Nd m []) = 1" |
"T_fold (Rt ((b, x) # xs)) = 1 + (T_fold x) + (T_fold (Rt xs))" |
"T_fold (Nd m ((b, x) # xs)) = 2 + (T_fold x) + (T_fold (Rt xs))"


theorem fold_sound: "eval (get_msg proc) = eval (fold proc)"
by (induction proc rule: get_msg.induct) auto

lemma T_fold_sz: "valid proc \<Longrightarrow> T_fold proc \<le> sz proc + nd proc"
apply (induction proc rule: T_fold.induct) 
  apply auto 
    using valid_children_node by force+

lemma T_fold_linear: 
"\<exists>a b. valid proc \<longrightarrow> T_fold proc \<le> a * (sz proc) + b"
using T_fold_sz nd_lf_sz_sound le_add2 by blast

section \<open>A summary of evaluation of the BC-logic terms 
and the folding process of the protocols\<close>

fun eval_proc :: "proc_trie => string" where
"eval_proc proc = eval (fold proc)"

fun T_eval_proc :: "proc_trie => nat" where
"T_eval_proc proc = T_fold proc + T_eval (fold proc)"


lemma T_eval_proc_sz_len: "valid proc \<Longrightarrow> T_eval_proc proc \<le> sz proc + nd proc + msg_len (fold proc)"
using fold_sound[of proc] T_fold_sz[of proc] linear_eval(1)[of "fold proc"] by simp

theorem T_eval_proc_linear: "\<exists>a1 a2 b. valid proc \<longrightarrow> T_eval_proc proc \<le> a1 * (sz proc) + a2 * msg_len (fold proc) + b"
using T_eval_proc_sz_len le_add2 by blast

section \<open>Unfinished: A few functions that access and modify the trie\<close>
fun trace :: "proc_trie => bl list => msg option" where
"trace (Rt []) [] = Some EMPTY" |
"trace (Rt []) (x # l) = None" |
"trace (Nd m []) [] = Some m" |
"trace (Nd m []) (x#l) = None" |
"trace (Rt ((b, t)#l)) [] = None" |
"trace (Rt ((b, t)#l)) (x#xs) = (
  if x = b then trace t xs else trace (Rt l) (x#xs)
)" |
"trace (Nd m ((b, t)#l)) [] = None" |
"trace (Nd m ((b, t)#l)) (x#xs) = (
  if x = b then trace t xs else trace (Rt l) (x#xs)
)"




end 