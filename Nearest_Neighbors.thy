(*
  File:     Nearest_Neighbors.thy
  Author:   Martin Rau, TU München
*)

section "Nearest Neighbor Search on the \<open>k\<close>-d Tree"

theory Nearest_Neighbors
imports 
  KDTree
begin

text \<open>
  Verifying nearest neighbor search on the k-d tree.
  Given a \<open>k\<close>-d tree and a point \<open>p\<close>, which might not be in the tree, find the points \<open>ms\<close> which are
  closest to \<open>p\<close> by some metric.
  The chosen metric is the euclidean distance between two points.
  To avoid working with roots I will work with the squared euclidean distance.
\<close>

subsection "Auxiliary Lemmas about \<open>sorted_wrt\<close>"

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  have "sorted_wrt f (take n xs @ drop n xs)" 
    using assms by simp
  thus "sorted_wrt f (take n xs)" "sorted_wrt f (drop n xs)"
    using sorted_wrt_append by blast+
qed

definition sorted_wrt_dist :: "('k::finite) point \<Rightarrow> 'k point list \<Rightarrow> bool" where
  "sorted_wrt_dist p \<equiv> sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. dist p\<^sub>0 p \<le> dist p\<^sub>1 p)"

lemma sorted_wrt_dist_last:
  assumes "sorted_wrt_dist p ps"
  shows "\<forall>q \<in> set ps. dist q p \<le> dist (last ps) p"
proof (cases "ps = []")
  case True
  thus ?thesis by simp
next
  case False
  then obtain ps' p' where [simp]:"ps = ps' @ [p']"
    using rev_exhaust by blast
  hence "sorted_wrt_dist p (ps' @ [p'])"
    using assms by blast
  thus ?thesis
    unfolding sorted_wrt_dist_def using sorted_wrt_append[of _ ps' "[p']"] by simp
qed

lemma sorted_wrt_dist_take_drop:
  assumes "sorted_wrt_dist p ps"
  shows "\<forall>q \<in> set (drop n ps). \<forall>r \<in> set (take n ps). dist r p \<le> dist q p"
  using assms unfolding sorted_wrt_dist_def by (metis append_take_drop_id sorted_wrt_append)

lemma sorted_wrt_dist_last_take:
  assumes "sorted_wrt_dist p ps" "ps \<noteq> []" "0 < n"
  shows "dist (last (take n ps)) p \<le> dist (last ps) p"
proof -
  have "last (take n ps) \<in> set ps"
    using assms(2,3) last_in_set[of "take n ps"] by (metis in_set_takeD le0 not_le take_eq_Nil)
  thus ?thesis
    using sorted_wrt_dist_last assms(1) by blast
qed


subsection "Neighbors Sorted by Distance"

fun upd_nbors :: "nat \<Rightarrow> ('k::finite) point \<Rightarrow> 'k point \<Rightarrow> 'k point list \<Rightarrow> 'k point list" where
  "upd_nbors 0 _ _ ps = []"
| "upd_nbors _ _ q [] = [q]"
| "upd_nbors m r q (p # ps) = (
    if dist q r \<le> dist p r then
      if m = 1 then [q]
      else q # p # take (m - 2) ps
    else
      p # upd_nbors (m - 1) r q ps
  )"

lemma length_nbors: 
  "length (upd_nbors m r q ps) = min m (length ps + 1)"
  by (induction m r q ps rule: upd_nbors.induct) auto

lemma length_nbors_eq_m:
  "set ps - set (upd_nbors m r q ps) \<noteq> {} \<Longrightarrow> length (upd_nbors m r q ps) = m"
  by (induction m r q ps rule: upd_nbors.induct) (auto simp: min_def, blast+)

lemma set_nbors:
  "length ps < m \<Longrightarrow> set (upd_nbors m r q ps) = set ps \<union> { q }"
  by (induction m r q ps rule: upd_nbors.induct) auto

lemma subset_nbors:
  "set (upd_nbors m r q ps) \<subseteq> set ps \<union> { q }"
  by (induction m r q ps rule: upd_nbors.induct) (auto, meson in_set_takeD)

lemma distinct_nbors:
  "distinct ps \<Longrightarrow> q \<notin> set ps \<Longrightarrow> distinct (upd_nbors m r q ps)"
  apply (induction m r q ps rule: upd_nbors.induct)
  apply (auto, simp_all add: in_set_takeD)
  using subset_nbors by fastforce

lemma sorted_wrt_dist_nbors:
  "sorted_wrt_dist r ps \<Longrightarrow> sorted_wrt_dist r (upd_nbors m r q ps)"
proof (induction m r q ps rule: upd_nbors.induct)
  case (3 m r q p ps)
  show ?case
  proof cases
    assume "dist q r \<le> dist p r"
    thus ?case
      using "3.prems" sorted_wrt_take in_set_takeD unfolding sorted_wrt_dist_def
      by (auto, fastforce, blast)
  next
    assume *: "\<not> dist q r \<le> dist p r"
    moreover have "\<forall>s \<in> set (p # ps). dist p r \<le> dist s r"
      using "3.prems" by (simp add: sorted_wrt_dist_def)
    ultimately have "\<forall>s \<in> set (upd_nbors m r q ps). dist p r \<le> dist s r"
      using subset_nbors by fastforce
    thus ?case
      using * 3 by (simp add: sorted_wrt_dist_def)
  qed
qed (auto simp: sorted_wrt_dist_def)

lemma dist_nbors_q:
  assumes "sorted_wrt_dist r ps" "q \<notin> set (upd_nbors m r q ps)" "0 < m"
  shows "dist (last (upd_nbors m r q ps)) r \<le> dist q r"
  using assms unfolding sorted_wrt_dist_def
  by (induction m r q ps rule: upd_nbors.induct) auto

lemma dist_nbors_ps:
  assumes "sorted_wrt_dist r ps" "0 < m"
  shows "\<forall>p \<in> set ps - set (upd_nbors m r q ps). dist (last (upd_nbors m r q ps)) r \<le> dist p r"
  using assms
proof (induction m r q ps rule: upd_nbors.induct)
  case (3 m r q p ps)
  show ?case
  proof cases
    assume *: "dist q r \<le> dist p r"
    show ?case
    proof cases
      assume "0 < m"
      have "\<forall>s \<in> set (drop (m - 2) (p # ps)). dist (last (take (m - 2) (p # ps))) r \<le> dist s r"
        using sorted_wrt_dist_take_drop[OF "3.prems"(1), of "m - 2"] last_in_set sledgehammer
      hence "\<forall>s \<in> set (drop (m - 1) ps). dist (last (upd_nbors (Suc m) r q (p # ps))) r \<le> dist s r"
        using * \<open>0 < m\<close> "3.prems"(1) by (auto simp: sorted_wrt_dist_def)
      moreover have "set (p # ps) - set (upd_nbors (Suc m) r q (p # ps)) \<subseteq> set (drop (m - 1) ps)"
        using * \<open>0 < m\<close> by (auto, metis UnE append_take_drop_id set_append)
      ultimately show ?case
        by blast
    next
      assume "\<not> 0 < m"
      thus ?case
        using * 3 by (auto simp: sorted_wrt_dist_def)
  next
    assume *: "\<not> dist q r \<le> dist p r"
    moreover have 0: "\<forall>s \<in> set (p # ps). dist p r \<le> dist s r"
      using "3.prems" by (simp add: sorted_wrt_dist_def)
    ultimately have 1: "\<forall>s \<in> set (upd_nbors m r q ps). dist p r \<le> dist s r"
      using subset_nbors by fastforce
    thus ?case
    proof cases
      assume "0 < m"
      hence "\<forall>p \<in> set ps - set (upd_nbors m r q ps). dist (last (upd_nbors m r q ps)) r \<le> dist p r"
        using * 3 by (simp add: sorted_wrt_dist_def)
      thus ?case
        using * \<open>0 < m\<close> 0 1 "3.prems"(2) by auto
    next
      assume "\<not> 0 < m"
      thus ?case
        using * 0 by simp
    qed
  qed
qed simp_all
 
lemma dist_nbors_length:
  assumes "sorted_wrt_dist p ps" "m \<le> length ps" "0 < m"
  shows "dist (last (upd_nbors m p q ps)) p \<le> dist (last ps) p"
  using assms
proof (induction m p q ps rule: upd_nbors.induct)
  case (3 m r q p ps)
  then show ?case
  proof cases
    assume "dist q r \<le> dist p r"
    thus ?case
      using 3 apply (auto)
      apply (simp add: order_trans sorted_wrt_dist_def)+
      by (metis diff_is_0_eq last_in_set set_take_subset sorted_wrt_dist_def sorted_wrt_dist_last subsetD take_eq_Nil)
  next
    assume *: "\<not> dist q r \<le> dist p r"
    moreover have 0: "\<forall>s \<in> set (p # ps). dist p r \<le> dist s r"
      using "3.prems" by (simp add: sorted_wrt_dist_def)
    ultimately have 1: "\<forall>s \<in> set (upd_nbors m r q ps). dist p r \<le> dist s r"
      using subset_nbors by fastforce
    thus ?case
    proof cases
      assume "0 < m"
      hence "dist (last (upd_nbors m r q ps)) r \<le> dist (last ps) r"
        using * 3 by (simp add: sorted_wrt_dist_def)
      thus ?case
        using * \<open>0 < m\<close> 0 1 "3.prems"(2) by auto
    next
      assume "\<not> 0 < m"
      thus ?case
        using * 0 by simp
    qed
  qed
qed auto


subsection "The Recursive Nearest Neighbor Algorithm"

fun nearest_nbors :: "nat \<Rightarrow> ('k::finite) point list \<Rightarrow> 'k point \<Rightarrow> 'k kdt \<Rightarrow> 'k point list" where
  "nearest_nbors m ps p (Leaf q) = (
    upd_nbors m p q ps
  )"
| "nearest_nbors m ps p (Node k v l r) = (
    if p$k \<le> v then
      let candidates = nearest_nbors m ps p l in
      if length candidates = m \<and> dist p (last candidates) \<le> dist v (p$k) then
        candidates
      else
        nearest_nbors m candidates p r
    else
      let candidates = nearest_nbors m ps p r in
      if length candidates = m \<and> dist p (last candidates) \<le> dist v (p$k) then
        candidates
      else
        nearest_nbors m candidates p l
  )"

lemma cutoff_r:
  assumes "invar (Node k v l r)"
  assumes "p$k \<le> v" "dist p c \<le> dist (p$k) v"
  shows "\<forall>q \<in> set_kdt r. dist p c \<le> dist p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt r"
  have "dist p c \<le> dist (p$k) v"
    using assms(3) by blast
  also have "... \<le> dist (p$k) v + dist v (q$k)"
    by simp
  also have "... = dist (p$k) (q$k)"
    using * assms(1,2) dist_real_def by auto
  also have "... \<le> dist p q"
    using dist_vec_nth_le by blast
  finally show "dist p c \<le> dist p q" .
qed

lemma cutoff_l:
  assumes "invar (Node k v l r)"
  assumes "v \<le> p$k" "dist p c \<le> dist v (p$k)"
  shows "\<forall>q \<in> set_kdt l. dist p c \<le> dist p q"
proof standard
  fix q
  assume *: "q \<in> set_kdt l"
  have "dist p c \<le> dist v (p$k)"
    using assms(3) by blast
  also have "... \<le> dist v (p$k) + dist (q$k) v"
    by simp
  also have "... = dist (p$k) (q$k)"
    using * assms(1,2) dist_real_def by auto
  also have "... \<le> dist p q"
    using dist_vec_nth_le by blast
  finally show "dist p c \<le> dist p q" .
qed


subsection "The Main Theorems"

lemma mnn_length:
  "length (nearest_nbors m ps p kdt) = min m (size_kdt kdt + length ps)"
  by (induction kdt arbitrary: ps) (auto simp: Let_def length_nbors)

lemma mnn_length_gt_0:
  "0 < m \<Longrightarrow> 0 < length (nearest_nbors m ps p kdt)"
  by (induction kdt arbitrary: ps) (auto simp: Let_def length_nbors)

lemma mnn_length_gt_eq_m:
  assumes "(set_kdt kdt \<union> set ps) - set (nearest_nbors m ps p kdt) \<noteq> {}"
  shows "length (nearest_nbors m ps p kdt) = m"
  using assms
  apply (induction kdt arbitrary: ps)
  apply (auto simp: length_nbors_eq_m length_nbors set_nbors min_def)
  apply (metis UnCI insertI1 le_SucI not_less set_nbors)
  apply (smt le_add2 min_def mnn_length subsetD)+
  done

lemma mnn_sorted:
  assumes "sorted_wrt_dist p ps"
  shows "sorted_wrt_dist p (nearest_nbors m ps p kdt)"
  using assms sorted_wrt_dist_nbors
  by (induction kdt arbitrary: ps) (auto simp: Let_def)

lemma mnn_set:
  shows "set (nearest_nbors m ps p kdt) \<subseteq> set_kdt kdt \<union> set ps"
  using subset_nbors
  by (induction kdt arbitrary: ps) (auto simp: Let_def, fastforce)

lemma mnn_distinct:
  assumes "invar kdt" "distinct ps" "set ps \<inter> set_kdt kdt = {}"
  shows "distinct (nearest_nbors m ps p kdt)"
  using assms
proof (induction kdt arbitrary: ps)
  case (Leaf p')
  thus ?case
    by (simp add: distinct_nbors)
next
  case (Node a s l r)
  let ?cl = "nearest_nbors m ps p l"
  let ?cr = "nearest_nbors m ps p r"
  have "set ps \<inter> set_kdt l = {} \<and> set ps \<inter> set_kdt r = {}"
    using Node.prems(3) by auto
  hence DCLR: "distinct ?cl \<and> distinct ?cr"
    using Node.IH(1,2) Node.prems(1,2,3) invar_l invar_r by blast
  have "set ?cl \<inter> set_kdt r = {} \<and> set ?cr \<inter> set_kdt l = {}"
    using Node.prems(1,3) mnn_set by fastforce
  hence "distinct (nearest_nbors m ?cl p r) \<and> distinct (nearest_nbors m ?cr p l)"
    using Node.IH(1,2) Node.prems(1,2) DCLR invar_l invar_r by blast
  thus ?case 
    using DCLR by (auto simp add: Let_def)
qed

lemma mnn_le_last_ps:
  assumes "invar kdt" "sorted_wrt_dist p ps" "m \<le> length ps" "0 < m"
  shows "dist (last (nearest_nbors m ps p kdt)) p \<le> dist (last ps) p"
  using assms
proof (induction kdt arbitrary: ps)
  case (Leaf p')
  thus ?case
    by (simp add: dist_nbors_length)
next
  case (Node a s l r)
  let ?cl = "nearest_nbors m ps p l"
  let ?cr = "nearest_nbors m ps p r"
  have "m \<le> length ?cl"
    using Node.prems(3) by (simp add: mnn_length)
  hence "dist (last (nearest_nbors m ?cl p r)) p \<le> dist (last ?cl) p"
    using mnn_sorted Node.IH(2) Node.prems(1,2,3,4) invar_r by blast
  hence IHLR: "dist (last (nearest_nbors m ?cl p r)) p \<le> dist (last ps) p"
    using Node.IH(1)[of ps] Node.prems invar_l mnn_length_gt_0 by auto
  have "m \<le> length ?cr"
    using Node.prems(3) by (simp add: mnn_length)
  hence "dist (last (nearest_nbors m ?cr p l)) p \<le> dist (last ?cr) p"
    using mnn_sorted Node.IH(1) Node.prems(1,2,3,4) invar_l by blast
  hence IHRL: "dist (last (nearest_nbors m ?cr p l)) p \<le> dist (last ps) p"
    using Node.IH(2)[of ps] Node.prems invar_r mnn_length_gt_0 by auto
  show ?case 
    using Node IHLR IHRL by (auto simp add: Let_def)
qed

theorem mnn_dist:
  assumes "invar kdt" "sorted_wrt_dist p ms" "set ms \<inter> set_kdt kdt = {}" "distinct ms" "0 < m"
  shows "\<forall>q \<in> set_kdt kdt \<union> set ms - set (nearest_nbors m ms p kdt). dist (last (nearest_nbors m ms p kdt)) p \<le> dist q p"
  using assms
proof (induction kdt arbitrary: ms)
  case (Leaf p')
  thus ?case
    using dist_nbors_q dist_nbors_ps by force
next
  case (Node a s l r)

  let ?cl = "nearest_nbors m ms p l"
  let ?cr = "nearest_nbors m ms p r"

  have IHL: "\<forall>q \<in> set_kdt l \<union> set ms - set ?cl. dist (last ?cl) p \<le> dist q p"
    using Node.IH(1) Node.prems invar_l invar_set by auto
  have IHR: "\<forall>q \<in> set_kdt r \<union> set ms - set ?cr. dist (last ?cr) p \<le> dist q p"
    using Node.IH(2) Node.prems invar_r invar_set by auto

  have SORTED_L: "sorted_wrt_dist p ?cl"
    using mnn_sorted Node.prems(2) by blast
  have SORTED_R: "sorted_wrt_dist p ?cr"
    using mnn_sorted Node.prems(2) by blast

  have DISTINCT_L: "distinct ?cl"
    using Node.prems mnn_distinct invar_set invar_l by fastforce
  have DISTINCT_R: "distinct ?cr"
    using Node.prems mnn_distinct invar_set invar_r
    by (metis inf_bot_right inf_sup_absorb inf_sup_aci(3) sup.commute)

  consider (A) "p$a \<le> s \<and> length ?cl = m \<and> dist p (last ?cl) \<le> dist s (p$a)"
         | (B) "p$a \<le> s \<and> \<not>(length ?cl = m \<and> dist p (last ?cl) \<le> dist s (p$a))"
         | (C) "s < p$a \<and> length ?cr = m \<and> dist p (last ?cr) \<le> dist s (p$a)"
         | (D) "s < p$a \<and> \<not>(length ?cr = m \<and> dist p (last ?cr) \<le> dist s (p$a))"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. dist (last ?cl) p \<le> dist q p"
      using Node.prems(1,2) cutoff_r by (metis dist_commute)
    thus ?thesis
      using IHL A by auto
  next
    case B

    let ?mnn = "nearest_nbors m ?cl p r"

    have "set ?cl \<subseteq> set_kdt l \<union> set ms" "set ms \<inter> set_kdt r = {}"
      using mnn_set Node.prems(1,3) by (simp add: mnn_set disjoint_iff_not_equal)+
    hence "set ?cl \<inter> set_kdt r = {}"
      using Node.prems(1) by fastforce
    hence IHLR: "\<forall>q \<in> set_kdt r \<union> set ?cl - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using Node.IH(2)[OF _ SORTED_L _ DISTINCT_L Node.prems(5)] Node.prems(1) invar_r by blast

    have "\<forall>n \<in> set ms - set ?cl. dist (last ?mnn) p \<le> dist n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "dist (last ?mnn) p \<le> dist (last ?cl) p"
        using mnn_le_last_ps SORTED_L invar_r Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?cl) p \<le> dist n p"
        using IHL * by blast
      thus "dist (last ?mnn) p \<le> dist n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt r \<union> set ms - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using IHLR by auto

    have "\<forall>q \<in> set_kdt l - set ?cl. dist (last ?mnn) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt l - set ?cl"

      hence "length ?cl = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "dist (last ?mnn) p \<le> dist (last ?cl) p"
        using mnn_le_last_ps SORTED_L invar_r Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?cl) p \<le> dist q p"
        using IHL * by blast
      thus "dist (last ?mnn) p \<le> dist q p"
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt l - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using IHLR by blast

    show ?thesis
      using B R L by auto
  next
    case C
    hence "\<forall>q \<in> set_kdt l. dist (last ?cr) p \<le> dist q p"
      using Node.prems(1,2) cutoff_l by (metis dist_commute less_imp_le)
    thus ?thesis
      using IHR C by auto
  next
    case D

    let ?mnn = "nearest_nbors m ?cr p l"

    have "set ?cr \<subseteq> set_kdt r \<union> set ms" "set ms \<inter> set_kdt l = {}"
      using mnn_set Node.prems(1,3) by (simp add: mnn_set disjoint_iff_not_equal)+
    hence "set ?cr \<inter> set_kdt l = {}"
      using Node.prems(1) by fastforce
    hence IHRL: "\<forall>q \<in> set_kdt l \<union> set ?cr - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using Node.IH(1)[OF _ SORTED_R _ DISTINCT_R Node.prems(5)] Node.prems(1) invar_l by blast

    have "\<forall>n \<in> set ms - set ?cr. dist (last ?mnn) p \<le> dist n p"
    proof standard
      fix n
      assume *: "n \<in> set ms - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "dist (last ?mnn) p \<le> dist (last ?cr) p"
        using mnn_le_last_ps SORTED_R invar_l Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?cr) p \<le> dist n p"
        using IHR * by blast
      thus "dist (last ?mnn) p \<le> dist n p"
        using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt l \<union> set ms - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using IHRL by auto

    have "\<forall>q \<in> set_kdt r - set ?cr. dist (last ?mnn) p \<le> dist q p"
    proof standard
      fix q
      assume *: "q \<in> set_kdt r - set ?cr"

      hence "length ?cr = m"
        using mnn_length_gt_eq_m by blast
      hence LAST: "dist (last ?mnn) p \<le> dist (last ?cr) p"
        using mnn_le_last_ps SORTED_R invar_l Node.prems(1,2,5) by (metis order_refl)
      have "dist (last ?cr) p \<le> dist q p"
        using IHR * by blast
      thus "dist (last ?mnn) p \<le> dist q p" 
        using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt r - set ?mnn. dist (last ?mnn) p \<le> dist q p"
      using IHRL by blast

    show ?thesis 
      using D R L by auto
  qed
qed


subsection "Nearest Neighbors Definition and Theorems"

definition nearest_neighbors :: "nat \<Rightarrow> ('k::finite) point \<Rightarrow> 'k kdt \<Rightarrow> 'k point list" where
  "nearest_neighbors m p kdt = nearest_nbors m [] p kdt"

theorem nearest_neighbors_length:
  "length (nearest_neighbors m p kdt) = min m (size_kdt kdt)"
  by (simp add: mnn_length nearest_neighbors_def)

theorem nearest_neighbors_sorted:
  "sorted_wrt_dist p (nearest_neighbors m p kdt)"
  using mnn_sorted unfolding nearest_neighbors_def sorted_wrt_dist_def by force

theorem nearest_neighbors_set:
  "set (nearest_neighbors m p kdt) \<subseteq> set_kdt kdt"
  unfolding nearest_neighbors_def using mnn_set by force

theorem nearest_neighbors_distinct:
  assumes "invar kdt"
  shows "distinct (nearest_neighbors m p kdt)"
  using assms by (simp add: mnn_distinct nearest_neighbors_def)

theorem nearest_neighbors:
  assumes "invar kdt" "mns = nearest_neighbors m p kdt"
  shows "\<forall>q \<in> (set_kdt kdt - set mns). \<forall>n \<in> set mns. dist n p \<le> dist q p"
proof (cases "0 < m")
  case True
  have "\<forall>q \<in> set_kdt kdt - set mns. dist (last mns) p \<le> dist q p"
    using nearest_neighbors_def mnn_dist[OF assms(1), of p "[]", OF _ _ _ True] assms(2)
    by (simp add: nearest_neighbors_def sorted_wrt_dist_def)
  hence "\<forall>q \<in> set_kdt kdt - set mns. \<forall>n \<in> set mns. dist n p \<le> dist q p"
    using assms(2) nearest_neighbors_sorted[of p m kdt] sorted_wrt_dist_last[of p mns] by force
  thus ?thesis
    using nearest_neighbors_def by blast
next
  case False
  hence "length mns = 0"
    using assms(2) unfolding nearest_neighbors_def by (auto simp: mnn_length)    
  thus ?thesis
    by simp
qed

end