section {* Introduction *}

theory Mereology
imports "~~/src/HOL/Algebra/Order"
begin

section {* Definitions *}

typedecl "i" -- "the type of individuals"

locale mereology  =
  fixes P:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<preceq>" 50)

begin

definition PP:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<prec>" 50) 
  where "x \<prec> y \<equiv> x \<preceq> y \<and> x \<noteq> y"

lemma PP_irreflexive: "\<not> x \<prec> x"
  by (simp add: PP_def)

lemma PP_asymmetric: "x \<prec> y \<longrightarrow> \<not> y \<prec> x" oops

definition overlap:: "i \<Rightarrow> i \<Rightarrow> bool" ("O")
  where "O x y \<equiv> \<exists> z. z \<preceq> x \<and> z \<preceq> y"

lemma overlap_symmetric: "O x y \<longrightarrow> O y x"
  using overlap_def by blast

definition disjoint:: "i \<Rightarrow> i \<Rightarrow> bool" ("D")
  where "D x y \<equiv> \<not> O x y"

lemma disjoint_symmetric: "D x y \<longrightarrow> D y x"
  using disjoint_def overlap_def by auto

definition underlap:: "i \<Rightarrow> i \<Rightarrow> bool" ("U")
  where "U x y \<equiv> \<exists> z. x \<preceq> z \<and> y \<preceq> z"

lemma underlap_symmetric: "U x y \<longrightarrow> U y x"
  using underlap_def by auto

definition sum:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<oplus>" 52)
  where "x \<oplus> y \<equiv> THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y"

lemma sum_commutative: "x \<oplus> y = y \<oplus> x"
proof -
  have "(THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y) = (THE z. \<forall> w. O w z \<longleftrightarrow> O w y \<or> O w x)"
    by metis
  thus ?thesis
    using sum_def by simp
qed

definition product:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<otimes>" 53)
  where "x \<otimes> y \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y" -- "product or intersection"

lemma product_commutative: "x \<otimes> y = y \<otimes> x"
proof -
  have  "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq>  x \<and> w \<preceq> y) = (THE z. \<forall> w. w \<preceq>  z \<longleftrightarrow> w \<preceq>  y \<and> w \<preceq> x)"
    by metis
  thus ?thesis
    using product_def by simp
qed

definition universe:: "i" ("u")
  where "u \<equiv> THE z. \<forall> w. w \<preceq> z"

definition difference:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<ominus>" 51)
  where "x \<ominus> y \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> D w y"

definition complement:: "i \<Rightarrow> i" ("\<midarrow>")
  where "\<midarrow> x \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"

definition general_sum:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<sigma>")
  where "\<sigma> F \<equiv> THE x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y)"

abbreviation general_sum_infix:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" [8] 9)
  where "\<sigma> x. F x \<equiv> \<sigma> F" --  "general sum or fusion of the Fs"

lemma sum_of_its_PPs: "\<exists> y. y \<prec> x \<longrightarrow> x = (\<sigma> z. z \<prec> x)"
  using PP_irreflexive by blast

definition general_product:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<pi>")
  where "\<pi> F \<equiv> \<sigma> x. \<forall> y. F y \<longrightarrow> x \<preceq> y"

abbreviation general_product_infix:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<pi>" [8] 9)
  where "\<pi> x. F x \<equiv> \<pi> F"

end

section {* Ground Mereology *}

locale ground_mereology = mereology +
 assumes P_reflexivity: "x \<preceq> x"
 assumes P_antisymmetry: "x \<preceq> y \<longrightarrow> y \<preceq> x \<longrightarrow> x = y"
 assumes P_transitivity: "x \<preceq> y \<longrightarrow> y \<preceq> z \<longrightarrow> x \<preceq> z"

begin

interpretation partial_order: partial_order "(|carrier = set i, eq = op =, le = op \<preceq>|)"
  using P_reflexivity P_antisymmetry P_transitivity by unfold_locales auto

lemma "x = y \<longleftrightarrow> x \<preceq> y \<and> y \<preceq> x"
  using P_antisymmetry P_reflexivity by auto

lemma "x = y \<longleftrightarrow> (\<forall> z. z \<preceq> x \<longleftrightarrow> z \<preceq> y)"
  using P_antisymmetry P_reflexivity by blast

lemma "x = y \<longleftrightarrow> (\<forall> z. x \<preceq> z \<longleftrightarrow> y \<preceq> z)"
  using P_antisymmetry P_reflexivity by blast

lemma PP_asymmetry: "x \<prec> y \<longrightarrow> \<not> y \<prec> x"
  by (simp add: PP_def P_antisymmetry)

lemma PP_transitivity: "x \<prec> y \<longrightarrow> y \<prec> z \<longrightarrow> x \<prec> z"
  by (metis PP_def PP_asymmetry P_transitivity)

lemma "x \<prec> y \<longleftrightarrow> x \<preceq> y \<and> \<not> y \<preceq> x"
  using PP_def P_antisymmetry by auto

lemma "x \<preceq> y \<and> y \<prec> z \<longrightarrow> x \<prec> z"
  using PP_def PP_transitivity by blast

lemma "x \<prec> y \<and> y \<preceq> z \<longrightarrow> x \<prec> z"
  using PP_def PP_transitivity by blast

lemma overlap_reflexive: "O x x"
  using overlap_def P_reflexivity by blast

lemma P_implies_overlap: "x \<preceq> y \<longrightarrow> O x y"
  using overlap_def P_reflexivity by auto

lemma "x \<preceq> y \<and> O x z \<longrightarrow> O y z"
  using overlap_def P_transitivity by blast

lemma "(\<forall> z. z \<preceq> x \<longrightarrow> O z y) \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  by (meson overlap_def P_transitivity P_implies_overlap)

lemma disjoint_irreflexive: "\<not> D x x"
  by (simp add: disjoint_def overlap_reflexive)

lemma "x \<preceq> y \<and> D y z \<longrightarrow> D x z"
  by (meson disjoint_def overlap_def P_transitivity)

lemma "U x x"
  using underlap_def P_reflexivity by blast

lemma  P_implies_underlap: "x \<preceq> y \<longrightarrow> U x y"
  using underlap_def P_reflexivity by auto

lemma "x \<preceq> y \<and> U y z \<longrightarrow> U x z"
  using underlap_def P_transitivity by blast

lemma "(\<forall> z. x \<preceq> z \<longrightarrow> U z y) \<longleftrightarrow> (\<forall> z. U z x \<longrightarrow> U z y)"
  by (metis underlap_def P_transitivity P_implies_underlap)

lemma product_idempotence: "x \<otimes> x = x"
proof -
  have "x \<otimes> x = (THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> x)"
    using product_def by simp
  also have  "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> x) = x"
  proof (rule the_equality)
    show "\<forall> w. w \<preceq> x \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> x)" by simp
    show "\<And> z. \<forall>w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> x) \<Longrightarrow> z = x"
      using P_antisymmetry P_reflexivity by blast
  qed
  finally show ?thesis
    by simp
qed

lemma product_intro: "(\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)) \<longrightarrow> x \<otimes> y = z"
proof
  assume antecedent: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
  hence "(THE v. \<forall> w. w \<preceq> v \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y) = z"
  proof (rule the_equality)
    show "\<And> v. \<forall> w. w \<preceq> v \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y) \<Longrightarrow> v = z "
      by (meson antecedent P_antisymmetry P_reflexivity)
  qed
  thus "x \<otimes> y = z"
    using product_def by auto
qed

lemma difference_intro: "(\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)) \<longrightarrow> x \<ominus> y = z"
proof
  assume antecedent: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
  hence "(THE v. \<forall> w. w \<preceq> v \<longleftrightarrow> (w \<preceq> x \<and> D w y)) = z"
  proof (rule the_equality)
    show "\<And>v. \<forall>w. (w \<preceq> v) = (w \<preceq> x \<and> D w y) \<Longrightarrow> v = z"
      by (meson antecedent P_antisymmetry P_reflexivity)
  qed
  thus "x \<ominus> y = z"
    by (simp add: difference_def)
qed

lemma disjoint_difference_absorption: "D x y \<longrightarrow> x \<ominus> y = x"
proof
  assume "D x y"
  hence "\<forall> w. w \<preceq> x \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
    by (meson disjoint_def overlap_def P_transitivity)
  with difference_intro show "x \<ominus> y = x"..
qed

lemma complement_intro: "(\<forall> w. w \<preceq> y \<longleftrightarrow> D w x) \<longrightarrow> (\<midarrow> x) = y"
proof
  assume antecedent: "\<forall> w. w \<preceq> y \<longleftrightarrow> D w x"
  hence "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) = y"
  proof (rule the_equality)
    show "\<And>z. \<forall>w. (w \<preceq> z) = D w x \<Longrightarrow> z = y"
      using antecedent P_antisymmetry P_reflexivity by blast
  qed
  thus "(\<midarrow> x) = y"
    using complement_def by auto
qed

end

section {* Minimal Mereology *}

locale minimal_mereology = ground_mereology +
  assumes weak_supplementation: "x \<prec> y \<longrightarrow> (\<exists> z. z \<preceq> y \<and> D z x)"

begin

lemma proper_weak_supplementation: "(\<forall> x. \<forall> y. x \<prec> y \<longrightarrow> (\<exists> z. z \<prec> y \<and> D z x))"
  by (metis disjoint_def disjoint_symmetric P_implies_overlap
PP_def weak_supplementation)

lemma company: "x \<prec> y \<longrightarrow> (\<exists> z. z \<noteq> x \<and> z \<prec> y)"
  using disjoint_irreflexive proper_weak_supplementation by force

lemma strong_company: "x \<prec> y \<longrightarrow> (\<exists> z. z \<prec> y \<and> \<not> z \<preceq> x)"
  by (meson disjoint_def P_implies_overlap proper_weak_supplementation)

end

section {* Extensional Mereology *}

locale extensional_mereology = ground_mereology +
  assumes strong_supplementation: "\<not> x \<preceq> y \<longrightarrow> (\<exists> z. z \<preceq> x \<and> D z y)"

begin

lemma PPs_principle:  "(\<exists> z. z \<prec> x) \<longrightarrow> (\<forall> z. z \<prec> x \<longrightarrow> z \<preceq> y) \<longrightarrow> x \<preceq> y"
  by (metis disjoint_def overlap_def PP_def P_reflexivity strong_supplementation)

lemma extensionality: "(\<exists> z. z \<prec> x \<or> z \<prec> y) \<longrightarrow> (\<forall> z. z \<prec> x \<longleftrightarrow> z \<prec> y) \<longrightarrow> x = y"
  by (meson PP_def P_antisymmetry PPs_principle)

lemma weak_supplementation: "x \<prec> y \<longrightarrow> (\<exists> z. z \<preceq> y \<and> D z x)"
  using PP_def P_antisymmetry strong_supplementation by blast

lemma Ps_of_Ps_overlap: "x \<preceq> y \<longleftrightarrow> (\<forall> z. z \<preceq> x \<longrightarrow> O z y)"
  using disjoint_def P_transitivity P_implies_overlap strong_supplementation by blast

lemma P_overlappers_overlap: "x \<preceq> y \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  by (meson overlap_def P_transitivity Ps_of_Ps_overlap)
lemma identity_overlap_eq: "x = y \<longleftrightarrow> (\<forall> z. O x z \<longleftrightarrow> O y z)"
  by (meson disjoint_def overlap_symmetric P_antisymmetry P_implies_overlap strong_supplementation)

lemma "x \<preceq> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> D z x)"
  by (metis disjoint_def P_transitivity overlap_def strong_supplementation)

lemma "x \<preceq> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> \<not> z \<preceq> x)"
  by (meson disjoint_def P_transitivity P_implies_overlap strong_supplementation)

lemma disjoin_equivalence: "x = y \<longleftrightarrow> (\<forall> z. D z x \<longleftrightarrow> D z y)"
  by (metis disjoint_def PP_def P_implies_overlap strong_supplementation weak_supplementation)

lemma sum_idempotence: "x \<oplus> x = x"
proof -
  have "x \<oplus> x = (THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w x)"
    using sum_def by simp
  also have "\<dots> = x"
  proof (rule the_equality)
    show "\<forall> w. O w x \<longleftrightarrow> (O w x \<or> O w x)" by simp
    show "\<And>z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w x) \<Longrightarrow> z = x"
      by (meson disjoint_def disjoin_equivalence)
  qed
  finally show "x \<oplus> x = x" by simp
qed

lemma sum_intro:
   "(\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> y \<oplus> z = x"
proof
  assume antecedent: "\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)"
  hence "(THE x. \<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) = x"
  proof (rule the_equality)
    show "\<And> a. \<forall>w. O w a \<longleftrightarrow> (O w y \<or> O w z) \<Longrightarrow> a = x"
      by (meson antecedent identity_overlap_eq overlap_symmetric)
  qed
  thus "y \<oplus> z = x"
    using sum_def by blast
qed

lemma universe_intro: "(\<forall> y. y \<preceq> x) \<longrightarrow> x = u"
  by (simp add: P_antisymmetry the_equality universe_def)

lemma general_sum_absorpotion: "(\<sigma> z. z \<preceq> x) = x"
proof -
  have "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. z \<preceq> x \<and> O z y)) = x"
  proof (rule the_equality)
    show "\<forall> y. O y x \<longleftrightarrow> (\<exists>z. z \<preceq> x \<and> O z y)"
      using overlap_symmetric P_overlappers_overlap by blast
    thus "\<And> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. z \<preceq> x \<and> O z y) \<Longrightarrow> v = x"
      by (metis sum_intro)
  qed
  thus "(\<sigma> z. z \<preceq> x) = x"
    by (simp add: general_sum_def)
qed

lemma general_sum_intro: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) \<longrightarrow> (\<sigma> x. F x) = z"
proof
  assume antecedent: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
  hence "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z"
  proof (rule the_equality)
    show "\<And> v. \<forall> y. O y v \<longleftrightarrow> (\<exists>x. F x \<and> O x y) \<Longrightarrow> v = z"
      by (metis antecedent sum_intro)
  qed
  thus "(\<sigma> v. F v) = z"
    using general_sum_def by blast
qed

lemma general_sum_idempotence: "(\<sigma> z. z = x) = x"
  by (metis (full_types) general_sum_intro overlap_symmetric)

lemma general_product_idempotence: "x = (\<pi> z. z = x)"
proof -
  have "(\<pi> z. z = x) = (\<sigma> z. \<forall> y. x = y \<longrightarrow> z \<preceq> y)"
    by (simp add: general_product_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y))"
    using general_sum_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y)"
      using overlap_symmetric P_overlappers_overlap by blast
    thus "\<And>z. \<forall> y. O y z = (\<exists>v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y) \<Longrightarrow> z = x"
      by (metis sum_intro)
  qed
  finally show "x = (\<pi> z. z = x)" by simp
qed

lemma general_product_absorption: "x = (\<pi> z. x \<preceq> z)"
proof -
  have "(\<pi> z. x \<preceq> z) = (\<sigma> z. \<forall> y. x \<preceq> y \<longrightarrow> z \<preceq> y)"
    by (simp add: general_product_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x \<preceq> j \<longrightarrow> v \<preceq> j)  \<and> O v y))"
    using general_sum_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall>j. x \<preceq> j \<longrightarrow> v \<preceq> j) \<and> O v y)"
      by (meson overlap_def P_reflexivity P_transitivity)
    thus "\<And>z. \<forall>y. O y z = (\<exists>v. (\<forall>j. x \<preceq> j \<longrightarrow> v \<preceq> j) \<and> O v y) \<Longrightarrow> z = x"
      by (metis P_antisymmetry P_implies_overlap Ps_of_Ps_overlap)
  qed
  finally show "x = (\<pi> z. x \<preceq> z)"
    by simp
qed

end

sublocale extensional_mereology \<subseteq> minimal_mereology
  by (simp add: ground_mereology_axioms minimal_mereology_axioms.intro minimal_mereology_def weak_supplementation)

subsection {* Closure Mereology *}

locale closure_mereology = ground_mereology +
  assumes sum_closure: "U x y \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
-- "sum closure"
  assumes product_closure: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
-- "product closure"

begin

lemma product_character: "O x y \<longrightarrow> (\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
proof
  assume "O x y"
  with product_closure have "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  then obtain z where z: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  with product_intro have "x \<otimes> y = z"..
  thus "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
    by (simp add: z)
qed

lemma P_of_first_factor: "O x y \<longrightarrow> x \<otimes> y \<preceq> x"
  using P_reflexivity product_character by blast

lemma P_of_second_factor: "O x y \<longrightarrow> x \<otimes> y \<preceq> y"
  using P_reflexivity product_character by blast

lemma "O x y \<and> z \<preceq> x \<otimes> y \<longrightarrow> z \<preceq> x"
  using product_character by blast

lemma "O x y \<and> z \<preceq> x \<otimes> y \<longrightarrow> z \<preceq> y"
  using product_character by blast

lemma "x \<preceq> y \<longrightarrow> x \<otimes> y = x"
  using P_antisymmetry P_reflexivity P_implies_overlap product_character by blast

lemma  "O x y \<and> x = x \<otimes> y \<longrightarrow> x \<preceq> y"
  using P_of_second_factor by force

lemma product_overlap_implies_overlap: "O x y \<and> O w (x \<otimes> y) \<longrightarrow> O w x"
  using overlap_def product_character by blast

lemma PP_of_first_factor: "x \<noteq> y \<and> O x y \<longrightarrow> x \<otimes> y \<prec> x \<or> x \<otimes> y \<prec> y"
  by (simp add: P_of_first_factor P_of_second_factor PP_def)

lemma product_association: "(\<exists> w. w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z) \<longrightarrow> x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
proof
  assume antecedent: "(\<exists> w. w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z)"
  hence "O y z"
    using overlap_def by auto
  with product_character have yz: "\<forall> w. w \<preceq> (y \<otimes> z) \<longleftrightarrow> (w \<preceq> y \<and> w \<preceq> z)"..
  hence "O x (y \<otimes> z)"
    by (simp add: antecedent overlap_def)
  with product_character have "\<forall> w. w \<preceq> (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> (y \<otimes> z))"..
  hence xyz: "\<forall> w. w \<preceq> (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z)"
    using yz by simp
  from antecedent have "O x y"
    using overlap_def by auto
  with product_character have xy: "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
  hence "O (x \<otimes> y) z"
    by (simp add: antecedent overlap_def)
  with product_character have "\<forall> w. w \<preceq> ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (w \<preceq> (x \<otimes> y)) \<and> w \<preceq> z"..
  hence  "\<forall> w. w \<preceq> ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z"
    using xy by simp
  thus "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
    using xyz P_antisymmetry P_reflexivity by blast
qed

end

section {* Closed Extensional Mereology *}

locale closed_minimal_mereology = closure_mereology + minimal_mereology

begin

lemma strong_supplementation: "\<not> x \<preceq> y \<longrightarrow> (\<exists> z. z \<preceq> x \<and> D z y)"
proof fix x y
  assume "\<not> x \<preceq> y"
  show "(\<exists> z. z \<preceq> x \<and> D z y)"
  proof cases
    assume "D x y"
    thus "(\<exists> z. z \<preceq> x \<and> D z y)"
      using P_reflexivity by auto
  next
    assume "\<not> D x y"
    hence "O x y"
      using disjoint_def by simp
    with product_character have product: "\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
    hence "x \<otimes> y \<prec> x"
      using \<open>\<not> x \<preceq> y\<close> P_reflexivity PP_def by auto
    with weak_supplementation have "\<exists> z. z \<preceq> x \<and> D z (x \<otimes> y)"..
    then obtain c where c: "c \<preceq> x \<and> D c (x \<otimes> y)"..
    hence "c \<preceq> x \<and> D c y"
      by (meson disjoint_def overlap_def P_transitivity product)
    thus "\<exists> z. z \<preceq> x \<and> D z y"..
  qed
qed

end

locale closed_extensional_mereology = extensional_mereology + closure_mereology

sublocale closed_extensional_mereology \<subseteq> closed_minimal_mereology
  by (simp add: closed_minimal_mereology_def closure_mereology_axioms minimal_mereology_axioms)

sublocale closed_minimal_mereology \<subseteq> closed_extensional_mereology
  by (simp add: closed_extensional_mereology_def closure_mereology_axioms
extensional_mereology_axioms.intro extensional_mereology_def ground_mereology_axioms
strong_supplementation)

context closed_extensional_mereology
begin

lemma underlapping_sum_character: "U x y \<longrightarrow> (\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y))"
proof
  assume "U x y"
  with sum_closure have "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"..
  then obtain a where a: "\<forall> w. O w a \<longleftrightarrow> (O w x \<or> O w y)"..
  with sum_intro have "x \<oplus> y = a"..
  thus "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)" using a by simp
qed

lemma conditonal_sum_associativity: 
"(\<exists> v. x \<preceq> v \<and> y \<preceq> v \<and> z \<preceq> v) \<longrightarrow>  x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
proof
  assume antecedent: "\<exists> v. x \<preceq> v \<and> y \<preceq> v \<and> z \<preceq> v"
  hence "U x y"
    using underlap_def by auto
  with underlapping_sum_character have xy: "(\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y))"..
   hence "U (x \<oplus> y) z"
    using underlap_def antecedent P_overlappers_overlap by auto
  with underlapping_sum_character have "(\<forall> w. O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> (O w (x \<oplus> y) \<or> O w z))"..
  hence xyz: "\<forall> w. O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)"
    using xy by simp  
  have "U y z"
    using antecedent underlap_def by auto
  with underlapping_sum_character have yz: "(\<forall> w. O w (y \<oplus> z) \<longleftrightarrow> (O w y \<or> O w z))"..
  hence "U x (y \<oplus> z)"
    using underlap_def antecedent P_overlappers_overlap by auto
  with underlapping_sum_character have "(\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w (y \<oplus> z)))"..
  hence "\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)"
    using yz by simp
  hence "\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow>  O w ((x \<oplus> y) \<oplus> z)"
    using xyz by simp
  thus "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    using P_overlappers_overlap P_antisymmetry by auto
qed

lemma sums_of_Ps_are_Ps: "x \<preceq> z \<and> y \<preceq> z \<longrightarrow> x \<oplus> y \<preceq> z"
proof
  assume "x \<preceq> z \<and> y \<preceq> z"
  hence "U x y"
    using underlap_def by blast
  with underlapping_sum_character have "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"..
  thus "x \<oplus> y \<preceq> z"
    using P_overlappers_overlap \<open>x \<preceq> z \<and> y \<preceq> z\<close> by auto
qed

lemma P_implies_absorption: "y \<preceq> x \<longrightarrow> x = x \<oplus> y"
  by (metis sum_intro P_overlappers_overlap)

end

section {* Closed Extensional Mereology with Universe *}

locale closure_mereology_with_universe = closure_mereology +
  assumes universe_closure: "\<exists> z. \<forall> x. x \<preceq> z"

begin

lemma universal_underlap: "U x y"
  by (metis underlap_def universe_closure)

lemma universal_sum_closure: "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
  by (simp add: sum_closure universal_underlap)

lemma universe_intro: "(\<forall> x. x \<preceq> z) \<longrightarrow> u = z"
proof
  assume "\<forall> x. x \<preceq> z"
  hence "(THE y. \<forall> x. x \<preceq> y) = z"
  proof (rule the_equality)
    show "\<And> y. \<forall> x. x \<preceq> y \<Longrightarrow> y = z"
      by (simp add: \<open>\<forall>x. x \<preceq> z\<close> P_antisymmetry)
  qed
  thus "u = z"
    by (simp add: universe_def)
qed

lemma universe_character: "\<forall> x. x \<preceq> u"
  using universe_closure universe_intro by blast

lemma "u \<preceq> x \<longrightarrow> u = x"
  by (simp add: P_antisymmetry universe_character)

lemma "\<not> u \<prec> x"
  by (simp add: P_antisymmetry PP_def universe_character)

lemma multiplicative_identity: "x \<otimes> u = x"
  by (simp add: product_intro universe_character)

end

locale closed_extensional_mereology_with_universe = closure_mereology_with_universe +
  closed_extensional_mereology

begin

lemma "x \<oplus> u = u"
  using P_implies_absorption sum_commutative universe_character by auto

lemma sum_character: "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"
  by (simp add: underlapping_sum_character universal_underlap)

lemma sum_associativity: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
  using conditonal_sum_associativity universe_character by blast

lemma first_summand_inclusion: "x \<preceq> x \<oplus> y"
  by (simp add: P_overlappers_overlap sum_character)

lemma second_summand_inclusion: "y \<preceq> x \<oplus> y"
  using first_summand_inclusion sum_commutative by fastforce

lemma  sum_is_P_iff_summands_are: "x \<oplus> y \<preceq> z \<longleftrightarrow> x \<preceq> z \<and> y \<preceq> z"
  using first_summand_inclusion P_transitivity second_summand_inclusion
sums_of_Ps_are_Ps by blast

lemma  disjoint_summands_are_PPs: "D x y \<longrightarrow> x \<prec> x \<oplus> y \<and> y \<prec> x \<oplus> y"
  by (metis disjoint_def disjoint_symmetric first_summand_inclusion P_implies_overlap
PP_def second_summand_inclusion)

lemma nonP_implies_proper_summand: "\<not> x \<preceq> y \<longrightarrow> y \<prec> x \<oplus> y"
  by (metis first_summand_inclusion PP_def second_summand_inclusion)

lemma distinct_iff_proper_summand: "x \<noteq> y \<longleftrightarrow> x \<prec> x \<oplus> y \<or> y \<prec> x \<oplus> y"
  using first_summand_inclusion PP_def second_summand_inclusion sum_idempotence by auto

lemma absorption_iff_P: "x = x \<oplus> y \<longleftrightarrow> y \<preceq> x"
  by (metis P_implies_absorption second_summand_inclusion)

lemma  disjoint_second_implies_P_first: "(x \<preceq> y \<oplus> z \<and> D x z) \<longrightarrow> x \<preceq> y"
proof
  assume antecedent: "x \<preceq> y \<oplus> z \<and> D x z"
  have "\<forall> w. O w (y \<oplus> z) \<longleftrightarrow> (O w y \<or> O w z)" using sum_character.
  thus "x \<preceq> y"
    by (meson antecedent disjoint_def overlap_symmetric P_overlappers_overlap Ps_of_Ps_overlap)
qed

lemma proper_sum_monotonicity: "x \<prec> y \<and> D y z \<longrightarrow> x \<oplus> z \<prec> y \<oplus> z"
  by (metis absorption_iff_P disjoint_second_implies_P_first PP_def sum_commutative 
second_summand_inclusion sum_is_P_iff_summands_are)

end

section {* Closed Extensional Mereology with Differences *}

locale closure_mereology_with_differences = closure_mereology +
  assumes difference_closure: "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"

begin

lemma difference_character:  "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y))"
proof
  assume "(\<exists> w. w \<preceq> x \<and> D w y)"
  with difference_closure have "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"..
  then obtain z where z: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  with difference_intro have "(x \<ominus> y) = z"..
  thus "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
    using z by simp
qed

end

locale closed_extensional_mereology_with_differences =
closed_extensional_mereology + closure_mereology_with_differences

begin

lemma proper_difference: "(O x y \<and> \<not> x \<preceq> y) \<longrightarrow> (x \<ominus> y) \<prec> x"
proof
  assume "O x y \<and> \<not> x \<preceq> y"
  hence "\<not> x \<preceq> y"..
  with strong_supplementation have "(\<exists> w. w \<preceq> x \<and> D w y)"..
  with difference_character have "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  thus "(x \<ominus> y) \<prec> x"
    using \<open>O x y \<and> \<not> x \<preceq> y\<close> disjoint_def P_reflexivity PP_def by auto
qed

lemma PP_implies_proper_difference: "x \<prec> y \<longrightarrow> y \<ominus> x \<prec> y"
  using overlap_symmetric P_implies_overlap proper_difference PP_asymmetry
PP_def by blast

lemma no_difference_implies_disjoint: "\<not> y \<preceq> x \<and> y \<ominus> x = y \<longrightarrow> D x y"
  using disjoint_def disjoint_symmetric proper_difference PP_def by blast

lemma proper_difference_absorption: "x \<prec> y \<longrightarrow> x \<oplus> (y \<ominus> x) = y"
proof
  assume "x \<prec> y"
  with weak_supplementation have "(\<exists> w. w \<preceq> y \<and> D w x)"..
  with difference_character have difference: "\<forall> w. w \<preceq> (y \<ominus> x) \<longleftrightarrow> (w \<preceq> y \<and> D w x)"..
  hence "U x (y \<ominus> x)"
    by (metis \<open>x \<prec> y\<close> PP_def underlap_def P_reflexivity)
  with underlapping_sum_character have "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w x \<or> O w (y \<ominus> x)"..
  hence "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w y \<or> (O w y \<and> D w x)"
    by (metis \<open>x \<prec> y\<close> difference disjoint_def P_overlappers_overlap overlap_def
overlap_symmetric PP_def)
  hence  "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w y"
    by blast
  thus "x \<oplus> (y \<ominus> x) = y"
    by (simp add: P_antisymmetry P_overlappers_overlap)
 qed  
  
lemma difference_absorbs_product: "O x y \<and> \<not> x \<preceq> y \<longrightarrow> x \<ominus> (x \<otimes> y) = x \<ominus> y"
proof
  assume "O x y \<and> \<not> x \<preceq> y"
  hence "\<not> x \<preceq> y"..
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w y"..
  with difference_character have right: "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  have "O x y" using \<open>O x y \<and> \<not> x \<preceq> y\<close>..
  with product_character have product: "\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  hence "\<not> x \<preceq> (x \<otimes> y)"
    using \<open>O x y \<and> \<not> x \<preceq> y\<close> by blast
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w (x \<otimes> y)"..
  with difference_character have left: "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> (w \<preceq> x \<and> D w (x \<otimes> y))".. 
  hence "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> (w \<preceq> x \<and> D w (x \<otimes> y))"
    by (simp add: disjoint_def)
  hence "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> w \<preceq> (x \<ominus> y)"
    using product right disjoint_def overlap_def P_transitivity by smt
  thus "x \<ominus> (x \<otimes> y) = x \<ominus> y"
    using P_antisymmetry P_reflexivity by blast
qed
  
lemma difference_monotonicity: "\<not> x \<preceq> z \<longrightarrow> x \<preceq> y \<longrightarrow> x \<ominus> z \<preceq> y \<ominus> z"
proof
  assume "\<not> x \<preceq> z"
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w z"..
  with difference_character have left: "(\<forall> w. w \<preceq> (x \<ominus> z) \<longleftrightarrow> (w \<preceq> x \<and> D w z))"..
  show "x \<preceq> y \<longrightarrow> x \<ominus> z \<preceq> y \<ominus> z"
  proof
    assume "x \<preceq> y"
    hence "\<not> y \<preceq> z"
      using \<open>\<not> x \<preceq> z\<close> P_transitivity by blast
    with strong_supplementation have "\<exists> w. w \<preceq> y \<and> D w z"..
    with difference_character have right: "(\<forall> w. w \<preceq> (y \<ominus> z) \<longleftrightarrow> (w \<preceq> y \<and> D w z))"..
    hence "\<forall> w. w \<preceq> (x \<ominus> z) \<longrightarrow> w \<preceq> (y \<ominus> z)"
      using P_transitivity \<open>x \<preceq> y\<close> left by blast
    thus "x \<ominus> z \<preceq> y \<ominus> z"
      using P_reflexivity by auto
  qed
qed

end

section {* Closed Extensional Mereology with Complements *}

locale closure_mereology_with_complements = closure_mereology +
  assumes complement_closure: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"

begin

lemma complement_character: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
proof
  assume "\<not> (\<forall> y. y \<preceq> x)"
  with complement_closure have "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"..
  then obtain a where a: "\<forall> w. w \<preceq> a \<longleftrightarrow> D w x"..
  hence "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) = a"
  proof (rule the_equality)
    show "\<And>z. \<forall>w. (w \<preceq> z) = D w x \<Longrightarrow> z = a"
      using a P_antisymmetry P_reflexivity by blast
  qed
  hence "(\<midarrow> x) = a"
    using complement_def by auto
  thus "(\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
    by (simp add: a)
qed

lemma disjoint_implies_overlaps_complement: "D x y \<longrightarrow> O x (\<midarrow> y)"
  using complement_character disjoint_def P_implies_overlap by blast

lemma difference_closure: "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"
proof
  assume antecedent: "(\<exists> w. w \<preceq> x \<and> D w y)"
  hence "\<not> (\<forall> z. z \<preceq> y)"
    using disjoint_def P_implies_overlap by blast
  with complement_character have comp: "\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y"..
  hence "O x (\<midarrow> y)"
    by (simp add: antecedent overlap_def)
  with product_character have "\<forall> w. w \<preceq> x \<otimes> \<midarrow> y \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> \<midarrow> y"..
  hence "\<forall> w. w \<preceq> x \<otimes> \<midarrow> y \<longleftrightarrow> w \<preceq> x \<and> D w y"
    using comp by blast
  thus "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
qed

end

sublocale closure_mereology_with_complements \<subseteq> closure_mereology_with_differences
  by (simp add: closure_mereology_axioms closure_mereology_with_differences.intro
closure_mereology_with_differences_axioms.intro difference_closure)

locale closed_extensional_mereology_with_complements = closed_extensional_mereology +
  closure_mereology_with_complements

begin

lemma complement_sums_disjoints: "x \<noteq> u \<longrightarrow> (\<sigma> z. D x z) = \<midarrow> x"
proof
  assume "x \<noteq> u"
  hence "\<not> (\<forall> y. y \<preceq> x)"
    using universe_intro by blast
  with complement_character have "\<forall> w. (w \<preceq> \<midarrow> x) \<longleftrightarrow> D w x"..
  hence "\<forall> y. O y (\<midarrow> x) \<longleftrightarrow> (\<exists> z. (D x z) \<and> O z y)"
    by (meson disjoint_symmetric overlap_symmetric P_overlappers_overlap)
  with general_sum_intro show "(\<sigma> z. D x z) = \<midarrow> x"..
qed

end

locale closed_extensional_mereology_with_universe_and_complements =
closed_extensional_mereology_with_universe + closed_extensional_mereology_with_complements 

begin

lemma univ_complement_character: "x \<noteq> u \<longrightarrow> (\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
  using complement_character universe_intro by blast

lemma unique_complement: "(\<exists>! z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) \<longleftrightarrow> x \<noteq> u"
proof
  assume  "(\<exists>! z. \<forall> w.  w \<preceq> z \<longleftrightarrow> D w x)"
  thus "x \<noteq> u"
    by (meson disjoint_def P_reflexivity P_implies_overlap universe_character)
next
  assume "x \<noteq> u"
  show "\<exists>! z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"
  proof
    show "\<forall> w. (w \<preceq> \<midarrow> x) \<longleftrightarrow> D w x"
      using \<open>x \<noteq> u\<close> univ_complement_character by simp
    show "\<And>z. \<forall>w. (w \<preceq> z) \<longleftrightarrow> D w x \<Longrightarrow> z = \<midarrow> x"
      using complement_intro by simp
  qed
qed

lemma complement_disjointness: "x \<noteq> u \<longrightarrow> D x (\<midarrow> x)"
  using disjoint_symmetric P_reflexivity univ_complement_character by blast

lemma additive_inverse: "x \<noteq> u \<longrightarrow> x \<oplus> (\<midarrow> x) = u"
proof
  assume "x \<noteq> u"
  with univ_complement_character have "(\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"..
  have "\<forall> w. O w (x \<oplus> (\<midarrow> x)) \<longleftrightarrow> (O w x \<or> O w (\<midarrow> x))" using sum_character.
  thus "(x \<oplus> (\<midarrow> x)) = u"
    by (metis \<open>\<forall>w. (w \<preceq> \<midarrow> x) = D w x\<close> disjoint_def P_overlappers_overlap P_implies_overlap universe_intro)
qed

lemma in_comp_iff_disjoint: "y \<noteq> u \<longrightarrow> x \<preceq> \<midarrow> y \<longleftrightarrow> D x y"
  by (simp add: univ_complement_character)

lemma double_comp_eq: "x \<noteq> u \<longrightarrow> x = (\<midarrow>(\<midarrow> x))"
  by (metis additive_inverse complement_disjointness disjoint_irreflexive
disjoint_second_implies_P_first first_summand_inclusion P_antisymmetry
univ_complement_character)

lemma prod_disj_imp_overlap_comp: "O w x \<and> O x y \<and> O x (\<midarrow>y) \<longrightarrow> D w (x \<otimes> y) \<longrightarrow> O w (x \<otimes> (\<midarrow>y))"
proof
  assume antecedent: "O w x \<and> O x y \<and> O x (\<midarrow> y)"
  hence "O w x"..
  with product_character have prodwx: "(\<forall> v. v \<preceq> (w \<otimes> x) \<longleftrightarrow> (v \<preceq> w \<and> v \<preceq> x))"..
  have "O x (\<midarrow> y)"
    using antecedent by blast
  with product_character have prod_comp: "(\<forall> w. w \<preceq> (x \<otimes> (\<midarrow> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> (\<midarrow> y)))"..
  from antecedent have "O x y" by blast
  with product_character have prodxy: "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
  show "D w (x \<otimes> y) \<longrightarrow> O w (x \<otimes> (\<midarrow>y))"
  proof
    assume disjoint: "D w (x \<otimes> y)"
    hence "y \<noteq> u"
      using antecedent disjoint_def multiplicative_identity by auto
    with univ_complement_character have comp: "\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y"..
    hence "w \<otimes> x \<preceq> x \<otimes> (\<midarrow> y)" using prodwx prodxy
      using antecedent disjoint disjoint_def overlap_def P_of_second_factor prod_comp by auto
    hence "w \<otimes> x \<preceq> w \<and> w \<otimes> x \<preceq> x \<otimes> (\<midarrow> y)"
      by (simp add: antecedent P_of_first_factor)
    thus "O w (x \<otimes> (\<midarrow>y))"
      using overlap_def by blast
  qed
qed

lemma T57:
"y \<noteq> u \<and> O x y \<and> \<not> x \<preceq> y \<longrightarrow> x = ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y)))"
proof
  assume antecedent: "y \<noteq> u \<and> O x y \<and> \<not> x \<preceq> y"
  hence "y \<noteq> u"..
  with univ_complement_character have comp: "(\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y)"..
  hence "O x (\<midarrow> y)"
    by (simp add: antecedent overlap_def strong_supplementation)
  with product_character have prod_comp: "\<forall> w. w \<preceq> x \<otimes> (\<midarrow> y) \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> (\<midarrow> y)"..
  from antecedent have "O x y \<and> \<not> x \<preceq> y"..
  hence "O x y"..
  with product_character have prod: "\<forall> w. w \<preceq> x \<otimes> y \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y"..
  from sum_character have "\<forall>w. O w ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y))) \<longleftrightarrow> (O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y)))".
  have "\<forall> w. O w x \<longleftrightarrow> O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
  proof
    fix w
    show "O w x \<longleftrightarrow> O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
    proof
      assume "O w x"
      with product_character have product: "\<forall> v. v \<preceq> w \<otimes> x \<longleftrightarrow> v \<preceq> w \<and> v \<preceq> x"..
      show "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
      proof cases
        assume "O w (x \<otimes> y)"
        thus "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"..
      next
        assume "\<not> O w (x \<otimes> y)"
        hence "O w (x \<otimes> (\<midarrow> y))"
          by (simp add: \<open>O w x\<close> \<open>O x (\<midarrow> y)\<close> antecedent disjoint_def prod_disj_imp_overlap_comp)
        thus "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"..
      qed
    next
      assume "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
      thus "O w x"
      proof (rule disjE)
        assume "O w (x \<otimes> y)"
        thus "O w x"
          using antecedent product_overlap_implies_overlap by blast
      next
        assume "O w (x \<otimes> (\<midarrow>y))"
        thus "O w x"
          using \<open>O x (\<midarrow> y)\<close> product_overlap_implies_overlap by blast
      qed
    qed
  qed
  thus " x = ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y)))"
    using sum_intro identity_overlap_eq by force
qed

lemma cancellation: "D x y \<longrightarrow> (x \<oplus> y) \<ominus> x = y"
proof
  assume "D x y"
  hence "y \<preceq> (x \<oplus> y) \<and> D y x"
    by (simp add: disjoint_symmetric second_summand_inclusion)
  hence  "(\<exists> w. w \<preceq> (x \<oplus> y) \<and> D w x)"..
  with difference_character have "(\<forall> w. w \<preceq> ((x \<oplus> y) \<ominus> x) \<longleftrightarrow> (w \<preceq> (x \<oplus> y) \<and> D w x))"..
  thus "(x \<oplus> y) \<ominus> x = y"
    by (metis \<open>y \<preceq> x \<oplus> y \<and> D y x\<close> disjoint_second_implies_P_first sum_commutative
P_antisymmetry P_reflexivity)
qed

end

locale closed_extensional_mereology_with_universe_and_differences =
closed_extensional_mereology_with_universe + closed_extensional_mereology_with_differences

begin

lemma complement_closure: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"
proof
  assume "\<not> (\<forall> y. y \<preceq> x)"
  hence "\<exists> w. w \<preceq> u \<and> D w x"
    using strong_supplementation universe_character by blast
  with difference_character have "\<forall> w. w \<preceq> u \<ominus> x \<longleftrightarrow> w \<preceq> u \<and> D w x"..
  hence "\<forall> w. w \<preceq> u \<ominus> x \<longleftrightarrow> D w x"
    by (simp add: universe_character)
  thus "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"..
qed

end

sublocale closed_extensional_mereology_with_universe_and_differences \<subseteq> closed_extensional_mereology_with_universe_and_complements
  by (simp add: closed_extensional_mereology_axioms closed_extensional_mereology_with_complements.intro
closed_extensional_mereology_with_universe_and_complements.intro closed_extensional_mereology_with_universe_axioms
closure_mereology_axioms closure_mereology_with_complements.intro closure_mereology_with_complements_axioms.intro complement_closure)

sublocale closed_extensional_mereology_with_universe_and_complements \<subseteq> closed_extensional_mereology_with_universe_and_differences
  by (simp add: closed_extensional_mereology_axioms closed_extensional_mereology_with_differences.intro
closed_extensional_mereology_with_universe_and_differences.intro closed_extensional_mereology_with_universe_axioms
closure_mereology_with_differences_axioms)

section {* General Mereology *}

text {* General Mereology is obtained from Ground Mereology by adding the axiom of fusion or
unrestricted composition @{cite "casati_Ps_1999"} p. 46:  *}

locale general_mereology = ground_mereology +
  assumes fusion: "(\<exists> x. F x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
-- "fusion or unrestricted composition"

begin
 
lemma sum_closure: "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w a \<or> O w b))"
proof -
  have "(\<exists> x. (x = a \<or> x = b)) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
    using fusion solve_direct.
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
    by blast
  thus "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w a \<or> O w b))"
    by (metis overlap_symmetric) 
qed

lemma universal_overlap: "\<exists> z. \<forall> x. O x z"
proof -
  have "(\<exists> x. x = x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y))"
    using fusion by fast
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y)"
    by simp
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. O x y)"
    by simp
  thus ?thesis
    by (metis overlap_def P_reflexivity)
qed

end

locale general_minimal_mereology = minimal_mereology + general_mereology -- "General Minimal Mereology"

subsection {* Classical Extensional Mereology *}

locale classical_extensional_mereology = extensional_mereology + general_mereology
begin

text {* Following proof from @{cite "pontow_note_2004"} pp. 202-3  *}

lemma general_sum_character: "(\<exists> x. F x) \<longrightarrow> (\<forall> y. y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w)))"
proof
  assume "(\<exists> x. F x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  with general_sum_intro have sum:  "(\<sigma> v. F v) = z "..
  show "\<forall> y. y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
  proof
    fix y
    show "y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
    proof
      assume "y \<preceq> (\<sigma> v. F v)"
      hence "y \<preceq> z"
        using sum by simp
      hence "O y z"
        using overlap_def P_reflexivity by auto
      hence "(\<exists> x. F x \<and> O x y)"
        using z by simp
      thus "(\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
        by (metis overlap_def P_reflexivity P_transitivity \<open>y \<preceq> z\<close> z)
    next
      assume "(\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
      hence "y \<preceq> z" using z
        by (meson disjoint_def strong_supplementation)
      thus "y \<preceq> (\<sigma> v. F v)"
        using sum by simp
    qed
  qed
qed

text {* Following proof from @{cite "pontow_note_2004"} pp. 204  *}

lemma product_closure: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
proof
  assume "O x y"
  hence common_P: "\<exists> z. (z \<preceq> x \<and> z \<preceq> y)"
    using overlap_def by simp
  have "(\<exists> v. (v \<preceq> x \<and> v \<preceq> y)) \<longrightarrow> (\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))  \<longleftrightarrow> (\<forall> z. z \<preceq> w \<longrightarrow> (\<exists> v. (v \<preceq> x \<and> v \<preceq> y) \<and> O v z)))"
    using general_sum_character.
  hence common_P_sum: "(\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (\<forall> z. z \<preceq> w \<longrightarrow> (\<exists> v. (v \<preceq> x \<and> v \<preceq> y) \<and> O v z)))"
    using common_P..
  have "\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
  proof
    fix w
    show "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
    proof
      assume "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))"
      hence "(\<forall> t. t \<preceq> w \<longrightarrow> (\<exists> v. v \<preceq> x \<and> v \<preceq> y \<and> O v t))"
        using common_P_sum by simp
      hence "\<forall> t. t \<preceq> w \<longrightarrow> (O t x \<and> O t y)"
        by (meson overlap_symmetric P_overlappers_overlap)
      thus "w \<preceq> x \<and> w \<preceq> y"
        using strong_supplementation P_transitivity disjoint_def by meson
    next
      assume "w \<preceq> x \<and> w \<preceq> y"
      thus "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))"
        using overlap_def P_reflexivity common_P_sum by fastforce
    qed
  qed
  thus "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
qed

lemma universe_closure: "\<exists> z. \<forall> x. x \<preceq> z"
  using disjoint_def universal_overlap strong_supplementation by blast

text {* Pontow p. 209: *}

lemma difference_closure: "(\<exists> w. w \<preceq> a \<and> D w b) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> a \<and> D w b))"
proof
  assume antecedent: "(\<exists> w. w \<preceq> a \<and> D w b)"
  have "(\<exists> x. (x \<preceq> a \<and> D x b)) \<longrightarrow> (\<forall> y. y \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. (v \<preceq> a \<and> D v b) \<and> O v w)))"
    using general_sum_character.
  hence sum: "\<forall> y. y \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. (v \<preceq> a \<and> D v b) \<and> O v w))"
    using antecedent..
  have "\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (w \<preceq> a \<and> D w b)"
  proof
    fix w
    show "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (w \<preceq> a \<and> D w b)"
    proof
      assume left: "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b))"
      have "\<forall> z. z \<preceq> w \<longrightarrow> O z a"
        using left overlap_symmetric P_overlappers_overlap sum by blast
      hence "w \<preceq> a"
        using strong_supplementation disjoint_def by blast
      have "\<forall> v. v \<preceq> w \<longrightarrow> \<not> v \<preceq> b"
        by (metis overlap_def disjoint_def P_transitivity sum left)
      hence "D w b"
        using overlap_def disjoint_def by simp
      with \<open>w \<preceq> a\<close> show "w \<preceq> a \<and> D w b"..
    next
      assume "w \<preceq> a \<and> D w b"
      thus "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b))"
        using overlap_symmetric P_implies_overlap sum by blast
    qed
  qed
  thus "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> a \<and> D w b))"..
qed

lemma complement_closure: "(\<exists> w. D w x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"
  by (meson difference_closure universe_closure)

end

sublocale classical_extensional_mereology \<subseteq> closed_extensional_mereology_with_universe_and_differences
proof (unfold_locales)
  show "\<And>x y. U x y \<longrightarrow> (\<exists>z. \<forall>w. O w z = (O w x \<or> O w y))" using sum_closure by simp
  show " \<And>x y. O x y \<longrightarrow> (\<exists>z. \<forall>w. (w \<preceq> z) = (w \<preceq> x \<and> w \<preceq> y))" using product_closure.
  show "\<exists>z. \<forall>x. x \<preceq> z" using universe_closure.
  show "\<And>x y. (\<exists>w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists>z. \<forall>w. (w \<preceq> z) = (w \<preceq> x \<and> D w y))" using difference_closure.
qed

context classical_extensional_mereology
begin


(* lemma T60: "(\<exists> y. x \<prec> y) \<longrightarrow> x = (\<pi> z. x \<prec> z)" nitpick [user_axioms] oops

lemma T61:
"(\<exists> x. \<forall> y. F y \<longrightarrow> x \<preceq> y) \<longrightarrow> (\<pi> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<preceq> x))" nitpick [user_axioms] oops


lemma T61a: "(\<sigma> x. \<forall> y. F y \<longrightarrow> x \<preceq> y) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<preceq> x))" nitpick oops

text {* It seems as if Simons thought "(THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<preceq> x))" is an alternative way
of defining general product, but the definitions are not equivalent. Really?! *}

*)

lemma general_sum_redef: "(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> x. F x) = z"
    using general_sum_intro by simp
  have "(THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)) = z"
  proof (rule the_equality)
    show "\<forall>y. z \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)"
    proof
      fix y
      show "z \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)"
      proof
        assume "z \<preceq> y" 
        thus "(\<forall> z. F z \<longrightarrow> z \<preceq> y)"
          using overlap_symmetric P_overlappers_overlap z by blast
      next
        assume "(\<forall> z. F z \<longrightarrow> z \<preceq> y)"
        thus "z \<preceq> y"
          using overlap_symmetric P_overlappers_overlap z by blast
      qed
    qed
    thus "\<And>x. \<forall>y. (x \<preceq> y) = (\<forall>z. F z \<longrightarrow> z \<preceq> y) \<Longrightarrow> x = z"
      using P_antisymmetry P_reflexivity by blast
  qed
  thus "(\<sigma> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y))" 
    using \<open>(\<sigma> x. F x) = z\<close> by metis
qed

lemma T66:
"(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "z = (\<sigma> x. F x)"
    using general_sum_intro by simp
  have "(THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z))) = z"
  proof (rule the_equality)
    show "(\<forall>y. F y \<longrightarrow> y \<preceq> z) \<and> (\<forall>y. O y z = (\<exists>z. F z \<and> O y z))"
      using overlap_symmetric P_overlappers_overlap z by blast
    thus " \<And>x. (\<forall>y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall>y. O y x = (\<exists>z. F z \<and> O y z)) \<Longrightarrow> x = z"
      by (metis sum_intro)
  qed
  thus "(\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))" 
    using \<open>z = (\<sigma> x. F x)\<close> by metis
qed

lemma "(\<exists> y. F y) \<longrightarrow> O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)"
proof
  assume "(\<exists> y. F y)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z"
    using general_sum_intro by simp
  thus "O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)" by (metis z)
qed

lemma T68: "D x (\<sigma> y. F y) \<longrightarrow> (\<forall> z. F z \<longrightarrow> D z x)"
proof
  assume antecedent: "D x (\<sigma> y. F y)"
  show "(\<forall> z. F z \<longrightarrow> D z x)"
  proof cases
    assume "\<exists> z. F z"
    with general_sum_character have sum: "\<forall> y. (y \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"..
    show "(\<forall> z. F z \<longrightarrow> D z x)"
    proof
      fix z
      show "F z \<longrightarrow> D z x"
      proof
        assume "F z"
        from sum have "(z \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> z \<longrightarrow> (\<exists> v. F v \<and> O v w))"..
        with \<open>F z\<close> have "(z \<preceq> (\<sigma> v. F v))"
          by (metis overlap_symmetric P_reflexivity Ps_of_Ps_overlap)
        with antecedent show "D z x" 
          by (metis disjoint_def overlap_symmetric P_overlappers_overlap)
      qed
    qed
  next
    assume "\<not> (\<exists> z. F z)"
    thus "\<forall> z. F z \<longrightarrow> D z x"
      by blast
  qed
qed

(*
lemma T70: "(\<sigma> x. F x) \<preceq> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))" nitpick oops *)

lemma "(\<exists> x. F x) \<and> (\<exists> x. G x) \<longrightarrow>
 (\<sigma> x. F x) \<preceq> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
proof
  assume "(\<exists> x. F x) \<and> (\<exists> x. G x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z"
    using general_sum_intro by simp
  have "(\<exists> x. G x)"
    by (simp add: \<open>(\<exists>x. F x) \<and> (\<exists>x. G x)\<close>)
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)"..
  hence "(\<sigma> y. G y) = z"
    using general_sum_intro by simp
  show "(\<sigma> x. F x) \<preceq> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
  proof
    assume "(\<sigma> x. F x) \<preceq> (\<sigma> y. G y)"
    thus "(\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
      by (metis T68 \<open>(\<sigma> y. G y) = z\<close> mereology.disjoint_def mereology.overlap_symmetric
P_overlappers_overlap P_implies_overlap z)
  qed
qed

end

end

