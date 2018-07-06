theory Mereotopology
imports Mereology
begin
section {* theories *}

subsection {* Ground Topology *}

locale T =
 fixes C :: "i \<Rightarrow> i \<Rightarrow> bool" ("C")--"Connectedness"
 assumes connection_reflexivity: "C x x" -- "reflexivity of connectedness "
 and connection_symmetry: "C x y \<longrightarrow> C y x" -- "symmetry of connectedness"

begin

definition E :: "i \<Rightarrow> i \<Rightarrow> bool" ("E") --"Enclosure"
  where "E x y \<equiv> \<forall>z. C z x \<longrightarrow> C z y"


lemma enclosure_reflexivity: "E x x"
  by (simp add: E_def)

lemma enclosure_transitivity: "E x y \<longrightarrow> E y z \<longrightarrow> E x z "
  by (simp add: E_def)

lemma connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y" nitpick oops

lemma
  assumes connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y"
  shows enclousre_antisymmetry: "E x y \<and> E y x \<longrightarrow> x = y"
    using E_def connection_extensional connection_symmetry by blast

end

section{* Ground Mereotopology *}

locale MT = ground_mereology + T +
  assumes monotonicity: "P x y \<longrightarrow> E x y"

begin

lemma "P x y \<longrightarrow> (\<forall>z. C x z \<longrightarrow> C z y)"
  using E_def monotonicity connection_symmetry by blast

lemma connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y" nitpick oops

lemma overlap_implies_connection: "O x y \<longrightarrow> C x y"
  using E_def monotonicity overlap_def connection_symmetry connection_reflexivity by blast

lemma  "C x y \<longrightarrow> O x y" nitpick oops

definition EC :: "i => i\<Rightarrow> bool" ("EC") -- "external connection"
  where "EC x y \<equiv> C x y \<and> D x y"

lemma external_connection_irreflexive: "\<not> EC x x"
  by (simp add: EC_def disjoint_irreflexive)

lemma external_connection_symmetric: "EC x y \<longrightarrow> EC y x"
  using EC_def connection_symmetry disjoint_symmetric by blast

definition IP :: "i => i\<Rightarrow> bool" ("IP") -- "Internal part - part of y connected only to overlappers of y"
  where
"IP x y \<equiv> P x y \<and> (\<forall>z. C z x \<longrightarrow> O z y)"

lemma internal_part_antisymmetry: "IP x y \<longrightarrow> IP y x \<longrightarrow> x = y"
  by (simp add: IP_def P_antisymmetry)

lemma internal_part_transitivity: "IP x y \<longrightarrow> IP y z \<longrightarrow> IP x z"
  using IP_def P_transitivity overlap_implies_connection by blast

definition TP :: "i \<Rightarrow> i \<Rightarrow> bool" ("TP") -- "Tangential part"
  where "TP x y \<equiv> P x y \<and> \<not> IP x y"

lemma tangential_part_reflexivity: "\<exists> y. TP y x \<longrightarrow> TP x x" by simp

lemma tangential_part_antisymmetry: "TP x y \<longrightarrow> TP y x \<longrightarrow> x = y"
  by (simp add: P_antisymmetry TP_def)

definition IO :: "i \<Rightarrow> i \<Rightarrow> bool" ("IO")--"Internal overlap"
  where
"IO x y \<equiv> \<exists> z. IP z x \<and> IP z y"

lemma IO_reflexive: "\<exists> y. IO y x \<longrightarrow> IO x x"
  by simp
lemma IO_symmetric: "IO x y \<longrightarrow> IO y x"
  using IO_def by blast

definition TO :: "i \<Rightarrow> i \<Rightarrow> bool" ("TO")--"tangential overlap"
  where
"TO x y \<equiv> O x y \<and> \<not>IO x y"

lemma TO_reflexive: "\<exists> y. TO y x \<longrightarrow> TO x x"
  by simp
lemma TO_symmetric: "TO x y \<longrightarrow> TO y x"
  using IO_symmetric TO_def overlap_symmetric by blast

definition IU :: "i\<Rightarrow>i\<Rightarrow> bool" ("IU")--"Internal underlap"
  where "IU x y \<equiv> \<exists>z. IP x z \<and> IP y z"

definition TU :: "i\<Rightarrow>i\<Rightarrow>bool" ("TU")--"Tangentially underlap"
  where "TU x y \<equiv> U x y \<and> \<not> IU x y"

definition IPP :: "i => i\<Rightarrow> bool" ("IPP")--"internal proper part"
  where "IPP x y \<equiv> IP x y \<and> \<not>(IP y x)"

definition TPP :: "i\<Rightarrow>i\<Rightarrow>bool" ("TPP")--"tangential proper part"
  where
"TPP x y \<equiv> TP x y \<and> \<not>( TP y x)"

definition SC :: "i \<Rightarrow> bool" ("SC") -- "Self-connectedness"
  where
"SC x \<equiv> \<forall> y.\<forall> z.(\<forall> w. O w x \<longleftrightarrow> O w y \<or> O w z) \<longrightarrow> C y z"

end 

section {* Closed Mereotopology *}

locale CMT = closure_mereology + MT +
  assumes connection_implies_underlap: "C x y \<longrightarrow> U x y "

lemma (in CMT) SCC: "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists>z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y))" nitpick [user_axioms] oops

text {* The failure of SCC in closed minimal mereotopology seems to be a minor error in Casati and Varzi. *}

locale CEMT = closed_extensional_mereology + CMT


section {* Classical Extensional Mereotopology *}

locale GEMT = classical_extensional_mereology + MT

begin

lemma C_implies_U: "C x y \<longrightarrow> U x y"
  by (simp add: universal_underlap)

lemma "\<forall> x. IP x u"
  by (simp add: IP_def P_implies_overlap universe_character)

lemma SC_def2:  "SC x \<longleftrightarrow> (\<forall> y z. x = (y \<oplus> z) \<longrightarrow> C y z)"
proof
  assume "SC x"
  hence "\<forall> y z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
    using SC_def by simp
  thus "(\<forall> y z. x = (y \<oplus> z) \<longrightarrow> C y z)"
    using sum_character by simp
next
  assume "\<forall> y z. x = (y \<oplus> z) \<longrightarrow> C y z"
  have "\<forall> y z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
  proof fix y
    show "\<forall> z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
    proof fix z
      show "(\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
      proof
        assume "\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)"
        with sum_intro have "(y \<oplus> z) = x"..
        thus "C y z" using \<open>\<forall>y z. x = y \<oplus> z \<longrightarrow> C y z\<close> by blast
      qed
    qed
  qed
  thus "SC x" using SC_def by simp
qed

lemma separation: "O x y \<longrightarrow> O x z \<longrightarrow> (P x (y \<oplus> z) \<longrightarrow> ((x \<otimes> y) \<oplus> (x \<otimes> z)) = x)" sorry (* Can you prove this? *)

lemma identity: "x \<oplus> y = w \<oplus> v \<longrightarrow> \<not> (O v x \<and> O w x \<or> O v y \<and> O w y) \<longrightarrow> x = w \<and> y = v \<or> x = v \<and> y = w"  sorry (* Can you prove this? *)

lemma connected_self_connected_sum: "(C x y \<and> SC x \<and> SC y) \<longrightarrow> SC (x \<oplus> y)"
proof
  assume "C x y \<and> SC x \<and> SC y"
  have "\<forall> v w. (x \<oplus> y) = (v \<oplus> w) \<longrightarrow> C v w"
  proof
    fix v
    show "\<forall> w. (x \<oplus> y) = (v \<oplus> w) \<longrightarrow> C v w"
    proof
      fix w
      show "(x \<oplus> y) = (v \<oplus> w) \<longrightarrow> C v w"
      proof
        assume "(x \<oplus> y) = (v \<oplus> w)"
        show "C v w"
        proof (cases)
          assume "O v x \<and> O w x \<or> O v y \<and> O w y"
          thus "C v w"
          proof (rule disjE)
            assume "O v x \<and> O w x"
            hence "P x (v \<oplus> w) \<longrightarrow>  x = ((x \<otimes> v) \<oplus> (x \<otimes> w))"
              by (simp add: \<open>O v x \<and> O w x\<close> overlap_symmetric separation)
            have "P x (v \<oplus> w)"
              by (metis \<open>x \<oplus> y = v \<oplus> w\<close> first_summand_inclusion)
            hence "x = ((x \<otimes> v) \<oplus> (x \<otimes> w))"
              using \<open>x \<preceq> v \<oplus> w \<longrightarrow> x = x \<otimes> v \<oplus> x \<otimes> w\<close> by auto
            hence "C (x \<otimes> v) (x \<otimes> w)"
              using SC_def2 \<open>C x y \<and> SC x \<and> SC y\<close> by blast
            hence "C v (x \<otimes> w)"
              by (metis P_of_first_factor T.E_def T_axioms \<open>O v x \<and> O w x\<close> connection_symmetry monotonicity product_commutative)
            thus "C v w"
              by (metis P_of_first_factor T.E_def T_axioms \<open>O v x \<and> O w x\<close> monotonicity product_commutative)
          next
            assume "O v y \<and> O w y"
            hence "P y (v \<oplus> w) \<longrightarrow>  y = ((y \<otimes> v) \<oplus> (y \<otimes> w))"
              by (simp add: \<open>O v y \<and> O w y\<close> overlap_symmetric separation)
            have "P y (v \<oplus> w)"
              by (metis \<open>x \<oplus> y = v \<oplus> w\<close> second_summand_inclusion)
            hence "y = ((y \<otimes> v) \<oplus> (y \<otimes> w))"
              using \<open>y \<preceq> v \<oplus> w \<longrightarrow> y = y \<otimes> v \<oplus> y \<otimes> w\<close> by auto
            hence "C (y \<otimes> v) (y \<otimes> w)"
              using SC_def2 \<open>C x y \<and> SC x \<and> SC y\<close> by blast
            hence "C v (y \<otimes> w)"
              by (metis E_def P_of_first_factor \<open>O v y \<and> O w y\<close> connection_symmetry monotonicity product_commutative)
            thus "C v w"
              by (metis E_def P_of_first_factor \<open>O v y \<and> O w y\<close> monotonicity product_commutative)
          qed
        next
          assume "\<not> (O v x \<and> O w x \<or> O v y \<and> O w y)"
          hence "x = w \<and> y = v \<or> x = v \<and> y = w"
            using identity \<open>x \<oplus> y = v \<oplus> w\<close> by auto
          thus "C v w"
            using \<open>C x y \<and> SC x \<and> SC y\<close> connection_symmetry by blast
        qed
      qed
    qed
  qed
  thus "SC (x \<oplus> y)" using SC_def2 by simp
qed

lemma "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists> z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y))"
proof
  assume "(C x y \<and> SC x \<and> SC y)"
  with connected_self_connected_sum have "SC (x \<oplus> y)"..
  have "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> O w x \<or> O w y" using sum_character.
  hence "SC (x \<oplus> y) \<and> (\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> O w x \<or> O w y)" 
    using \<open>SC (x \<oplus> y)\<close> by simp
  thus "\<exists> z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y)"..
qed

definition i :: "(i \<Rightarrow> i)" ("\<^bold>i")--"interior"
  where "\<^bold>i x \<equiv> \<sigma> z. IP z x"

lemma interior_fusion: "(\<exists> y. IP y x) \<longrightarrow> (\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y))" using fusion.

lemma interior_intro: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)) \<longrightarrow> (\<^bold>i x) = a"
proof -
  have "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)) \<longrightarrow> (\<sigma> z. IP z x) = a" using general_sum_intro.
  thus ?thesis using i_def by simp
qed

lemma interior_character: "(\<exists> y. IP y x) \<longrightarrow> (\<forall> y. O y (\<^bold>i x) \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y))"
proof
  assume antecedent: "(\<exists> y. IP y x)"
  with interior_fusion have "\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  then obtain v where v: "\<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  with interior_intro have "(\<^bold>i x) = v"..
  thus "(\<forall> y. O y (\<^bold>i x) \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y))"
    using v by blast
qed

lemma interior_is_part: "(\<exists> y. IP y x) \<longrightarrow> P (\<^bold>i x) x" -- "the interior of an individual is part of it"
proof
  assume "(\<exists> y. IP y x)"
  with interior_fusion have "\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  then obtain a where a: "\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  with interior_intro have "(\<^bold>i x) = a"..
  thus "P (\<^bold>i x) x"
    by (metis IP_def P_overlappers_overlap a overlap_symmetric)
qed

lemma interior_overlaps: "(\<exists> y. IP y x) \<longrightarrow> O (\<^bold>i x) x"
  by (simp add: P_implies_overlap interior_is_part)
lemma interior_connects:  "(\<exists> y. IP y x) \<longrightarrow> C (\<^bold>i x) x"
  using P_implies_overlap interior_is_part overlap_implies_connection by blast
lemma encloses_interior:  "(\<exists> y. IP y x) \<longrightarrow> E (\<^bold>i x) x"
  by (simp add: interior_is_part monotonicity)

lemma "(\<exists> y. IP y x) \<longrightarrow> (\<exists> y. IP y z) \<longrightarrow> P z x \<longrightarrow> P (\<^bold>i z) (\<^bold>i x)" nitpick oops

definition e :: "(i\<Rightarrow>i)" ("e") -- "exterior"
  where "e x \<equiv> \<^bold>i (\<midarrow> x)"

lemma exterior_closure: "(\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> (\<exists> a. \<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<midarrow> x) \<and> O z y))" sorry (* prove this! *)

lemma exterior_intro: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<midarrow> x) \<and> O z y)) \<longrightarrow> (e x) = a"
proof
  assume "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<midarrow> x) \<and> O z y))"
  with interior_intro have "(\<^bold>i (\<midarrow> x)) = a"..
  thus "(e x) = a"
    using e_def by simp
qed

lemma exterior_character: "(\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> (\<forall> y. O y (e x) \<longleftrightarrow> (\<exists> z. IP z (\<midarrow> x) \<and> O z y))" sorry (* prove this! *)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> \<not> P (e x) x"
  using e_def P_implies_overlap in_comp_iff_disjoint interior_is_part disjoint_def by fastforce

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> \<not> P x (e x)"
  by (metis e_def P_implies_overlap P_overlappers_overlap complement_disjointness interior_is_part disjoint_def)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> D x (e x)"
  using complement_disjointness P_overlappers_overlap extensional_mereology_axioms
exterior_character interior_character interior_is_part disjoint_def by blast

definition c :: "i\<Rightarrow>i" ("c")--"closure"
  where
"c x \<equiv> \<midarrow> (e x)"

lemma closure_intro:  "(\<forall> y. P y a \<longleftrightarrow> D y (e x)) \<longrightarrow> (c x) = a"
  by (metis P_antisymmetry P_implies_overlap P_overlappers_overlap P_reflexivity c_def
complement_character disjoint_def overlap_def overlap_symmetric overlap_def overlap_reflexive)

lemma closure_character: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> (\<forall> y. P y (c x) \<longleftrightarrow> D y (e x))" sorry (* prove this *)

lemma closure_closure: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> (\<exists> a. \<forall> y. P y a \<longleftrightarrow> D y (e x))"
proof
  assume antecedent: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x))"
  with closure_character have "(\<forall> y. P y (c x) \<longleftrightarrow> D y (e x))"..
  thus "(\<exists> a. \<forall> y. P y a \<longleftrightarrow> D y (e x))"..
qed

lemma closure_inclusion: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> P x (c x)"
  using closure_character disjoint_symmetric e_def in_comp_iff_disjoint interior_is_part by fastforce

lemma closure_overlap: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> O x (c x)"
  by (simp add: P_implies_overlap closure_inclusion)

lemma closure_connection: "x \<noteq> u \<and> (\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> C x (c x)"
  by (simp add: closure_overlap overlap_implies_connection)

definition b :: "i\<Rightarrow>i" ("b")--"boundary"
  where "b x \<equiv> \<midarrow> (\<^bold>i x \<oplus> e x)"

lemma boundary_closure: "(\<^bold>i x \<oplus> e x) \<noteq> u \<longrightarrow> x \<noteq> u \<longrightarrow> (\<exists> z. IP z x) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x)) \<longrightarrow> (\<exists> a. \<forall> z. P z a \<longleftrightarrow> D z (\<^bold>i x \<oplus> e x))" sorry  (* prove this *)

lemma boundary_intro : "(\<forall> w. P w a \<longleftrightarrow> D w (\<^bold>i x \<oplus> e x)) \<longrightarrow> b x = a" (* Very good work on proving this in the last version *)
  by (metis P_antisymmetry P_implies_overlap P_reflexivity b_def complement_character disjoint_def)

lemma boundary_character: "(\<^bold>i x \<oplus> e x) \<noteq> u \<longrightarrow> x \<noteq> u \<longrightarrow> (\<exists> z. IP z x) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x)) \<longrightarrow> (\<forall> z. P z (b x) \<longleftrightarrow> D z (\<^bold>i x \<oplus> e x))" sorry (*prove this*)

text {* The following axioms are from Varzi "Parts, Wholes and Part-Whole Relations: The Prospects of Mereotopology page 273: *}

definition OP :: "i \<Rightarrow> bool" ("OP")--"open"
  where "OP x \<equiv> \<^bold>i x = x"

definition CL :: "i \<Rightarrow> bool" ("CL") -- "closed"
  where "CL x \<equiv> c x = x"

end

locale GEMTC = GEMT + 
  assumes C4: "CL x \<and> CL y \<longrightarrow> CL (x \<oplus> y)" 
  assumes C5: "(\<forall> x. F x \<longrightarrow> Cl x) \<longrightarrow> (\<exists> z. \<forall> y. F y \<longrightarrow> z \<preceq> y) \<longrightarrow> CL (\<pi> z. F z)"

begin

lemma C4': "OP x \<and> OP y \<longrightarrow> z = x \<otimes> y \<longrightarrow> OP z"  sorry (* can your prove this? *)

lemma C5': "(\<exists> x. F x) \<longrightarrow> (\<forall> x. F x \<longrightarrow> OP x) \<longrightarrow> OP (\<sigma> x. F x)"  sorry (* can you prove this? *)

lemma interior_inclusion : "\<exists> y. IP y x \<longrightarrow> P (\<^bold>i x) x"
  by (simp add: IP_def)

lemma interior_idempotence: "\<exists> y. IP y x \<longrightarrow> \<^bold>i (\<^bold>i x) = \<^bold>i x"
  by (metis IP_def P_overlappers_overlap interior_character internal_part_antisymmetry overlap_reflexive)

lemma interior_distributes_over_product: 
"(\<exists> z. IP z (x \<otimes> y)) \<and> (\<exists> z. IP z x) \<and> (\<exists> z. IP z y) \<longrightarrow> \<^bold>i (x \<otimes> y) = \<^bold>i x \<otimes> \<^bold>i y" sorry (* This proof might be a hard one. *)

lemma closure_inclusion: "(\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> P x (c x)" sorry (* can you prove this? *)

lemma closure_idempotence: "(\<exists> y. IP y (\<midarrow> x)) \<longrightarrow> c (c x) = c x"  sorry (* can you prove this? *)

lemma closure_distributes_over_sum:
"(\<exists> z. IP z (\<midarrow>(x \<oplus> y))) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x)) \<longrightarrow> (\<exists> z. IP z (\<midarrow> y)) \<longrightarrow> c (x \<oplus> y) = c x \<oplus> c y" sorry (* This proof might be a hard one. *)

lemma boundary_sharing:
  assumes "(\<^bold>i x \<oplus> e x) \<noteq> u \<longrightarrow> x \<noteq> u \<longrightarrow> (\<exists> z. IP z x) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x))"
  shows  "b x = b (\<midarrow> x)"  sorry  (* can your prove this? *)

lemma boundary_idempotence: 
  assumes "(\<^bold>i x \<oplus> e x) \<noteq> u \<longrightarrow> x \<noteq> u \<longrightarrow> (\<exists> z. IP z x) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x))"
  shows "b (b x) = b x"  sorry  (* can your prove this? *)

lemma boundary_distributes_over_sum:
  assumes "(\<^bold>i x \<oplus> e x) \<noteq> u \<longrightarrow> x \<noteq> u \<longrightarrow> (\<exists> z. IP z x) \<longrightarrow> (\<exists> z. IP z (\<midarrow> x))"
  shows "b (x \<otimes> y) \<oplus> b (x \<oplus> y) = b x \<oplus> b y"  sorry (* can your prove this? *)

(* These lemmas look helpful - well done: *)

lemma p_intro : "(\<forall>z. P a z \<longleftrightarrow> (P z (\<^bold>i x) \<and> P z (\<^bold>i y))) \<longrightarrow> ((\<^bold>i x) \<otimes> (\<^bold>i y)) = a"
  by (metis (full_types) P_antisymmetry P_implies_overlap complement_disjointness disjoint_def universe_closure universe_intro)

lemma p : "(\<forall>z. P a z \<longleftrightarrow> (P z x \<and> P z y)) \<longrightarrow> (x \<otimes> y) = a"
  by (metis P_antisymmetry P_implies_overlap disjoint_def in_comp_iff_disjoint universe_closure)

lemma pi : "(\<exists>w. IP a w \<and> (\<forall>v. P w v \<longleftrightarrow> P v x \<and> P v y)\<longrightarrow> a = \<^bold>i (x \<otimes> y))"
  by (meson P_antisymmetry P_reflexivity)

lemma pi2 : "(\<forall>z. O z a \<longleftrightarrow> (\<exists>w. IP w (x \<otimes> y) \<and> O w z))\<longrightarrow> \<^bold>i (x \<otimes> y) = a" sledgehammer oops

lemma Px : "\<exists>w. IP (x \<otimes> y) w \<longrightarrow> (\<forall>v. P w v \<longleftrightarrow> P v x \<and> P v y)" sledgehammer oops

lemma "(\<forall>v.\<exists>w. P w v \<and> P v x \<and> P v y \<longrightarrow> P w x \<and> P w y)"
  by auto

lemma Pi3 : "\<exists>w. IP (x \<otimes> y) w \<longrightarrow> P w x \<and> P w y"
  using IP_def by blast

lemma pp : "(\<exists>z. IP z (x \<otimes> y)) \<longrightarrow> P (\<^bold>i (x \<otimes> y)) (x \<otimes> y)"
  using interior_is_part by auto

lemma "\<not> (\<forall> x. C x a) \<longrightarrow> (\<forall> y. P y (e a) \<longleftrightarrow> \<not> C y a)"  oops

lemma "x \<noteq> u \<longrightarrow> (\<forall> y. P y (c x) \<longleftrightarrow> P y x \<or> (\<forall> z. P z y \<longrightarrow> C z x))"  oops

lemma  C_iff_O_orEC: "C x y \<longleftrightarrow> (O x y \<or> EC x y)"
  using EC_def disjoint_def overlap_implies_connection by blast

lemma  "EC x y \<longrightarrow> (\<exists> y. IP y (\<midarrow> x))"  oops

(* The following theses are still the main ones left to prove. But I don't feel we can attack it until
we at least understand the informal idea behind it. I will find out about this for you. *)

lemma C_implies_O_c:  "C x y \<longrightarrow> (O x (c y) \<or> O (c x) y)"  oops

lemma EC_implies_O_c: "((\<exists> z. IP z (\<midarrow> x)) \<or> (\<exists> z. IP z (\<midarrow> y))) \<longrightarrow> 
EC x y \<longrightarrow> (O x (c y) \<or> O (c x) y)"
proof 
  assume "(\<exists> z. IP z (\<midarrow> x)) \<or> (\<exists> z. IP z (\<midarrow> y))"
  thus "EC x y \<longrightarrow> (O x (c y) \<or> O (c x) y)"
  proof (rule disjE)
    assume "\<exists> z. IP z (\<midarrow> x)"
    show "EC x y \<longrightarrow> (O x (c y) \<or> O (c x) y)"
    proof
      assume "EC x y"
      hence "x \<noteq> u"
        using EC_def P_implies_overlap disjoint_def overlap_symmetric universe_character by blast
      hence "x \<noteq> u \<and> (\<exists> z. IP z (\<midarrow> x))" using \<open>\<exists>z. IP z (\<midarrow> x)\<close>..
      with closure_closure have "(\<exists> a. \<forall> y. P y a \<longleftrightarrow> D y (e x))"..
      then obtain a where a: "\<forall> y. P y a \<longleftrightarrow> D y (e x)"..
      with closure_intro have "(c x) = a"..
      hence "O (c x) y" sorry
      thus "O x (c y) \<or> O (c x) y"..
    qed
  next
    assume "(\<exists> z. IP z (\<midarrow> y))"
    show "EC x y \<longrightarrow> (O x (c y) \<or> O (c x) y)"
    proof
      assume "EC x y"
      hence "O x (c y)" sorry
      thus "O x (c y) \<or> O (c x) y"..
    qed
  qed
qed

lemma "C x y \<longleftrightarrow> (O x y \<or> (O x (c y) \<or> O (c x) y))" nitpick oops

lemma "C x y \<longleftrightarrow> (O x y \<or> (O x (c y) \<or> O (c x) y))"
proof
  assume "C x y"
  show "O x y \<or> (O x (c y) \<or> O (c x) y)"
  proof
    cases
    assume "O x y"
    thus "O x y \<or> (O x (c y) \<or> O (c x) y)"..
  next assume "D x y"
    hence "EC x y" using EC_def \<open>C x y\<close> by blast
    hence "(O x (c y) \<or> O (c x) y)"
      using EC_implies_O_c by blast
    thus "(O x y \<or> (O x (c y) \<or> O (c x) y))"..
  qed
next
  assume "O x y \<or> (O x (c y) \<or> O (c x) y)"
  thus "C x y" 
  proof (rule disjE)
    assume "O x y"
    thus "C x y" by (simp add: overlap_imnplies_connection)
  next
    assume "(O x (c y) \<or> O (c x) y)"
    thus "C x y"
    proof (rule disjE)
      assume "O x (c y)"
      show "C x y"
      proof cases
        assume "y = u"
        hence "O x y"
          by (simp add: T11 T51a)
        thus "C x y" by (simp add: overlap_imnplies_connection)
      next
        assume "y \<noteq> u"
        thus "C x y"  sorry
      qed
        next
          assume "O (c x) y"
      show "C x y"
      proof
        cases
        assume "x = u"
        thus "C x y" using T10 T11 T51a overlap_imnplies_connection by blast
        next
          assume "x \<noteq> u"
          thus "C x y"  sorry
        qed
      qed
    qed
  qed

lemma "(\<exists> z. IP z x) \<and> (\<exists> z. IP z y) \<longrightarrow> EC x y \<longrightarrow> C z y \<and> \<not> C (\<^bold>i x) (\<^bold>i y)" oops

lemma "C x y \<longleftrightarrow> (O x y \<or> (O x (c y) \<or> O (c x) y))" oops

lemma  "x \<noteq> u \<and> (\<exists> z. IP z (\<midarrow> x)) \<and> y \<noteq> u \<and> (\<exists> z. IP z (\<midarrow> y)) \<longrightarrow>
 C x y \<longleftrightarrow> (O x y \<or> (O x (c y) \<or> O (c x) y))" sledgehammer oops

lemma (in GEmonotonicity) "x \<noteq> u \<and> (\<exists> z. IP z (\<midarrow> x)) \<and> y \<noteq> u \<and> (\<exists> z. IP z (\<midarrow> y)) \<longrightarrow>
 C x y \<longleftrightarrow> (O x y \<or> (O x (c y) \<or> O (c x) y))" sledgehammer oops

definition SSC :: "i\<Rightarrow>bool" ("SSC")
  where
"SSC x \<equiv> SC x \<and> SC (\<^bold>i x) "

definition MSSC :: "(i\<Rightarrow>bool)" ("MSSC")
  where
"MSSC x \<equiv> SSC x \<and> (\<forall>y. (SSC y \<and> O y x) \<longrightarrow> P y x)"

end
