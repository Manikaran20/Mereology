section {* Introduction *}

theory Mereology
imports Main
begin

text {* This is a presentation in Isabelle/HOL of \emph{Classical Extensional Mereology}. The
presentation is based on those in ``Parts'' by Peter Simons @{cite "simons_parts:_1987"}
and ``Parts and Places'' by Roberto Casati and Achille Varzi @{cite "casati_parts_1999"}.
Some corrections and important proofs are from @{cite "pontow_note_2004"} *}

text {* Please note that this is an extremely ROUGH DRAFT. *}

section {* Ground Mereology *}

text {* Ground Mereology (M) introduces parthood as a primitive relation amongst individuals.
It's assumed that parthood is a partial ordering relation - that is reflexive, symmetric and
transitive  @{cite "casati_parts_1999"}, p. 36:  *}

typedecl i -- "the type of individuals"

locale M =
  fixes P:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes R: "x \<^bold>\<le> x" -- "reflexivity of parthood "
    and  AS: "x \<^bold>\<le> y \<longrightarrow> y \<^bold>\<le> x \<longrightarrow> x = y" -- "antisymmetry of parthood"
    and  T: "x \<^bold>\<le> y \<longrightarrow> y \<^bold>\<le> z \<longrightarrow> x \<^bold>\<le> z" -- "transitivity of parthood"

begin

text {* The following relations are defined in terms of parthood @{cite "casati_parts_1999"}, p. 36-7: *}

definition PP:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<^bold><" 50) 
  where "x \<^bold>< y \<equiv> x \<^bold>\<le> y \<and> \<not> y \<^bold>\<le> x" -- "proper parthood"
definition O:: "i \<Rightarrow> i \<Rightarrow> bool" ("O")
  where "O x y \<equiv> \<exists> z. z \<^bold>\<le> x \<and> z \<^bold>\<le> y" -- "overlap"
definition D:: "i \<Rightarrow> i \<Rightarrow> bool" ("D")
  where "D x y \<equiv> \<not> O x y" -- "disjointness"
definition U:: "i \<Rightarrow> i \<Rightarrow> bool" ("U")
  where "U x y \<equiv> \<exists> z. x \<^bold>\<le> z \<and> y \<^bold>\<le> z" -- "underlap"

text {* As are the following operations on individuals @{cite "casati_parts_1999"}, p. 43-5: *}

definition S:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<^bold>+" 52)
  where "x \<^bold>+ y \<equiv> THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y" -- "sum or fusion"
definition T:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<^bold>\<times>" 53)
  where "x \<^bold>\<times> y \<equiv> THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<and> O w y" -- "product or intersection"
definition u:: "i" ("u")
  where "u \<equiv> THE z. \<forall> w. P w z" -- "universe"
definition M:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<^bold>-" 51)
  where "x \<^bold>- y \<equiv> THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<and> \<not> O w y" -- "difference"
definition C:: "i \<Rightarrow> i" ("\<^bold>\<not>")
  where "\<^bold>\<not> x \<equiv> (u \<^bold>- x)" -- "complement"

text {* And the operations of general sum and product @{cite casati_parts_1999}, p. 46:  *}

definition \<sigma>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<sigma>")
  where "\<sigma> F \<equiv> THE z. (\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
abbreviation \<sigma>x:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" [8] 9)
  where "\<sigma> x. F x \<equiv> \<sigma> F" --  "general sum or fusion of the Fs"
definition \<pi>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<pi>")
  where "\<pi> F \<equiv> THE z. (\<forall> x. F x \<longrightarrow> z \<^bold>\<le> x)" -- "general products @{cite casati_parts_1999}, p. 46"
abbreviation \<pi>x:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<pi>" [8] 9)
  where "\<pi> x. F x \<equiv> \<pi> F"  --  "general sum or product of the Fs"

(*
definition OX:: "i \<Rightarrow> i \<Rightarrow> bool" ("OX")
  where "OX x y \<equiv> O x y \<and> \<not> x \<^bold>\<le> y"
definition UX:: "i \<Rightarrow> i \<Rightarrow> bool" ("UX")
  where "UX x y \<equiv> U x y \<and> \<not> y \<^bold>\<le> x"
definition PO:: "i \<Rightarrow> i \<Rightarrow> bool" ("PO" )
  where "PO x y \<equiv> OX x y \<and> OX y x"
definition PU:: "i \<Rightarrow> i \<Rightarrow> bool" ("PU")
  where "PU x y \<equiv> UX x y \<and> UX y x"
*)

text {* Note that the symbols for part, proper part, sum, product, difference and complement are
distinguished by bold font. *}

end

section {* Minimal Mereology *}

text {* Minimal mereology (MM) adds to ground mereology the axiom of weak supplementation
@{cite "casati_parts_1999"}, p. 39: *}

locale MM = M +
  assumes WS: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)" -- "weak supplementation"

text {* Weak supplementation is sometimes stated with parthood rather than proper parthood
in the consequent. The following lemma in ground mereology shows that the two definitions
are equivalent, given anti-symmetry: *}

lemma (in M)  "(x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)) \<longleftrightarrow> (x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>\<le> y \<and> D z x))"
  by (metis AS D_def O_def PP_def R)

text {* The following two lemmas are weaker supplementation principles taken from Simons
@{cite "simons_parts:_1987"}, p. 27. The names \emph{company} and \emph{strong company}
are from Varzi's \emph{Stanford Encyclopedia of Philosophy} entry on mereology
@{cite "varzi_mereology_2016"}. *}

lemma (in MM)  C: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<noteq> x \<and> z \<^bold>< y)" by (metis WS D_def O_def R) -- "company"
lemma (in MM)  SC: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> \<not> z \<^bold>\<le> x)" by (metis WS D_def O_def R) -- "strong company"

text {* Minimal Mereology is not strong enough to proved the \emph{Proper Parts Principle},
according to which if x has a proper part, and every proper part of x is a part of y, then
x is a part of y @{cite "simons_parts:_1987"} p. 28:  *}

lemma (in MM) PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y" -- "proper parts principle"
  nitpick [user_axioms]  oops

  text {* The proper parts principle is Simons way of expressing \emph{extensionality}, which is
not a theorem of Minimal Mereology either: *}

lemma (in M) E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y" -- "extensionality"
  nitpick oops

text {* The failure of weak supplementation to entail the proper parts principle or extensionality
motivates a stronger axiom, to which we turn in the next section.  *}

(*
lemma (in M)
  assumes PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y"
  shows E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y"
  using PPP AS PP_def by blast

lemma (in MM) 
 assumes E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y"
 shows PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y" 
  nitpick oops
*)

section {* Extensional Mereology *}

text {* Extensional Mereology (EM) adds the axiom of strong supplementation @{cite "casati_parts_1999"}, p. 39: *}

locale EM = M +
  assumes SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" -- "strong supplementation"

text {* Extensional Mereology (@{text "EM"} is so called because it entails the proper parts principle
@{cite "simons_parts:_1987"} p. 29: *}

lemma (in EM) PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y"
  by (metis SS D_def R O_def PP_def T)

text {* And thus extensionality proper @{cite "casati_parts_1999"} p. 40: *}

lemma (in EM)
 E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y" -- "extensionality"
  by (metis R O_def D_def AS PP_def SS)

text {* In the context of the other axioms, strong supplementation entails weak supplementation
@{cite "simons_parts:_1987"}, p. 29:  *}

lemma (in M) SStoWS:
  assumes SS: "\<And>x. \<And> y. \<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
-- "assumes strong supplementation"
  shows WS: "\<And>x. \<And>y. x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)"
-- "shows weak supplementation"
  by (metis AS D_def O_def PP_def R assms)

text {* But not vice versa:  *} 

lemma (in M) WStoSS:
  assumes WS: "\<And>x. \<And>y. x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)"
-- "assumes weak supplementation"
  shows SS: "\<And>x. \<And> y. \<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
-- "shows strong supplementation"
  nitpick oops

text {* So Extensional Mereology is stronger than Minimal Mereology @{cite "casati_parts_1999"} p. 43:  *}

sublocale EM \<subseteq> MM using T SS SStoWS by (metis MM.intro MM_axioms.intro M_axioms)
sublocale MM \<subseteq> EM nitpick oops

lemma (in MM)
  assumes PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y"
  shows SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" nitpick oops

(*
  text {* Two alternative formulations of the strong supplementation axiom, which are equivalent given
transitivity are @{cite "pontnow_note_2004"} p. 198: *}

lemma (in M) "((\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y) \<longleftrightarrow> (\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y))"
  using D_def by blast
lemma (in M)
"((\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y) \<longleftrightarrow> (\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y))"
  by (metis O_def D_def R T)

lemma (in M) assumes SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
  shows "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  using D_def SS by blast

lemma (in M) assumes "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  shows "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  using O_def R assms by blast

lemma (in M) assumes "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" 
  shows SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
  by (meson D_def O_def T assms)

lemma (in EM) "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" using SS D_def by blast
lemma (in EM) "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" by (metis SS T D_def O_def)

*)

section {* Closure Mereology *}

text {* Closure Mereology adds to Ground Mereology the axioms of sum closure and product closure
 @{cite "casati_parts_1999"} p. 43: *}

locale CM = M +
  assumes SC: "U x y \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))" -- "sum closure"
  assumes PC: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" -- "product closure"

text {* Combining Closure Mereology with Minimal Mereology yields the theory known as
Closure Minimal Mereology @{term "CMM"} whereas combining Closure Mereology with Extensional
Mereology obtains \emph{Closed Extensional Mereology} @{term "CEM"}
@{cite "casati_parts_1999"} p. 43: *}

locale CMM = CM + MM
locale CEM = EM + CM

text {* In Closed Minimal Mereology, the product closure axiom and weak supplementation jointly
entail strong supplementation.  The proof verified here is from Pontow @{cite "pontow_note_2004"} p. 200: *}

lemma (in CMM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
proof fix x y
  assume "\<not> x \<^bold>\<le> y"
  show "(\<exists> z. z \<^bold>\<le> x \<and> D z y)"
  proof cases
    assume "D x y"
    thus "(\<exists> z. z \<^bold>\<le> x \<and> D z y)" using R by auto
  next
    assume "\<not> D x y"
    hence "O x y" using D_def by simp
    hence "\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using PC by simp
    then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"..
    hence "z \<^bold>< x" using PP_def R \<open>\<not> x \<^bold>\<le> y\<close> by auto
    hence "(\<exists> w. w \<^bold>< x \<and> D w z)" using WS by simp
    then obtain w where "w \<^bold>< x \<and> D w z"..
    hence "w \<^bold>\<le> x \<and> D w y" by (meson D_def O_def PP_def T z)
    thus "(\<exists> z. z \<^bold>\<le> x \<and> D z y)"..
  qed
qed

(* Later I might  add here the proof of the proper parts principle from products on 
@{cite "simons_parts:_1987"} p. 33 *)

text {* Because Strong Supplementation is provable in Closed Minimal Mereology, it follows that
Closed Extensional Mereology and Closed Minimal Mereology are the same theory 
@{cite "casati_parts_1999"} p. 44: *}

sublocale CEM \<subseteq> CMM by (simp add: CMM.intro CM_axioms MM_axioms)
sublocale CMM \<subseteq> CEM  by (simp add: CEM.intro CM_axioms EM.intro EM_axioms.intro M_axioms SS)

text {* Closure Mereology with Universe (CMU) is obtained by adding  an axiom ensuring existence
of a universe @{cite "casati_parts_1999"} p. 44:  *}

locale CMU = CM +
  assumes U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" -- "universe"

text {* And adding Extensional Mereology (or Minimal Mereology) to this theory results in
Closed Extensional Mereology with Universe @{text "CEMU"}: *}

locale CEMU = EM + CMU

text {* In Closure Extensional Mereology with Universe, it's possible to derive a strengthening of
the sum axiom, since everything underlaps everything else: *}

lemma (in CEMU) EU: "U x y" using U_def U by auto -- "everything underlaps"
lemma (in CEMU) SSC: "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))" using EU SC by simp
 -- "strengthened sum closure"

(*
text {* Does CEMU entail the existence of differences? I should think yes, since the difference
between a and b is the sum of the elements of a that overlap b. However, if a has infinitely many
elements, the sum may not be guaranteed to exist by the product axiom. This might explain why
nitpick does not find a counterexample: *}

lemma (in CEMU) D: "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" oops

*)

section {* General Mereology *}

text {* General Mereology is obtained from Ground Mereology by adding the axiom of fusion or
unrestricted composition @{cite "casati_parts_1999"} p. 46:  *}

locale GM = M +
  assumes F: "(\<exists> x. F x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))" -- "fusion or unrestricted composition"

text {* Substituting @{text "x = a \<or> x = b"} for @{text "F x"} in the fusion axiom allows the derivation of
an unrestricted version of sum closure @{text "GS"}, and so of course sum closure itself, as follows:  *}

lemma (in GM) FS:
"(\<exists> x. (x = a \<or> x = b)) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
  using F solve_direct.
lemma (in GM) GFS: "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
  using FS by blast
lemma (in M) GFStoGS:
  assumes GFS: "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
  shows "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w a \<or> O w b))" by (metis O_def GFS)
lemma (in GM) GS: "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
  using GFS GFStoGS by simp
lemma (in GM) S: "U x y \<longrightarrow> (\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
  using GS by simp

text {* But product closure cannot be derived: *}

lemma (in GM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
  nitpick [show_all] oops

  text {* It follows that General Mereology does not encompass Closure Mereology, contrary to
Simons @{cite "simons_parts:_1987"} p. 36 and Casati and Varzi @{cite "casati_parts_1999"} p. 46
(this point is discussed in detail by Pontow @{cite "Pontow_note_2004"}: *}

sublocale GM \<subseteq> CM nitpick [show_all] oops

text {* It's possible to prove from fusion in General Mereology that there is something that
overlaps everything: *}

lemma (in GM) "\<exists> z. \<forall> x. O x z" -- "something overlaps everything"
proof -
  have "(\<exists> x. x = x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y))" using F by fast
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y)" by simp
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. O x y)" by simp
  thus ?thesis by (metis O_def R)
qed

text {* But it doesn't follow that there is a universe, let alone a unique universe. If for example,
there is just an infinite ascending chain, then everything overlaps everything else, but there isn't
a particular thing which everything is a part of, since for anything in particular, the things above it
are not part of the chain: *}

lemma (in GM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" nitpick oops

text {* The existence of differences is not guaranteed either: *}

lemma (in GM) D:  "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" nitpick oops

subsection {* General Minimal Mereology *}

text {*  Call the combination of General Mereology with weak supplementation General Minimal
Mereology, or @{term "GMM"}: *}

locale GMM = MM + GM -- "General Minimal Mereology"

text {* Although Strong Supplementation can be derived from Weak Supplementation in Closed Minimal
Mereology  via the product axioms, it cannot be derived in General Minimal Mereology, since the
product axiom itself still cannot be derived in General Minimal Mereology:  *}

lemma (in GMM) SS:   "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" nitpick oops
lemma (in GMM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" nitpick [show_all] oops

text {* Nor can the existence of a universe or differences be proved in General Minimal Mereology: *}

lemma (in GMM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" nitpick oops
lemma (in GMM) D: "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" nitpick oops

section {* Classical Extensional Mereology *}

text {* Classical Extensional Mereology @{text "GEM"} is simply Extensional Mereology combined
with General Mereology  @{cite "casati_parts_1999"} p. 46: *}

locale GEM = EM + GM

text {* The presence of strong supplementation in Classical Extensional Mereology enables the derivation of 
product closure from fusion. The following proof is from Pontow  @{cite "pontow_note_2004"} pp. 202-3.  *}

text {* The proof begins by substitutions @{text "z \<^bold>\<le> a \<and> z \<^bold>\<le> b"} for @{text "F"} in the fusion axiom,
to give the existence of a sum of all the parts of @{text "a"} and @{text "b"}: *}

lemma (in GM) FP: "(\<exists> z. (z \<^bold>\<le> a \<and> z \<^bold>\<le> b)) \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (\<exists> x. (x \<^bold>\<le> a \<and> x \<^bold>\<le> b) \<and> O x w))"
  using F solve_direct.

text {* Three lemmas are helpful before proceeding with the proof proper. First, strong supplementation
is needed to proceed from the fact that z is \emph{a} sum of the Fs to the fact that z is \emph{the}
sum of the Fs:  *}

lemma (in EM) atothesum:
  assumes asum: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
  shows thesum: "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z"
proof (rule the_equality)
  show "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using asum.
  show "\<And>v. \<forall>y. O y v = (\<exists>x. F x \<and> O x y) \<Longrightarrow> v = z"  by (metis SS AS D_def O_def R asum)
qed

text {* Using this lemma, we can show that if something overlaps z just in case it overlaps an F,
then it is the sum of the Fs: *}

lemma (in EM) UGS: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) \<longrightarrow> (\<sigma> x. F x) = z"
proof
  assume "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
  hence "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z" using atothesum by simp
  thus "(\<sigma> v. F v) = z" using \<sigma>_def by blast
qed

text {* With this lemma in hand, we can proceed with a final lemma the proof from
Pontow @{cite "pontow_note_2004"} pp. 202-3, according to which if there is an F, then everything
is part of the sum of the Fs just in case every part of it overlaps with an F. *}

lemma (in GEM) PS: "(\<exists> x. F x) \<longrightarrow> (\<forall> y. y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w)))"
proof
  assume "(\<exists> x. F x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence \<sigma>: "(\<sigma> v. F v) = z " using UGS by simp
  show "\<forall> y. y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
  proof
    fix y
    show "y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
      proof
        assume "y \<^bold>\<le> (\<sigma> v. F v)"
        hence "y \<^bold>\<le> z" using \<sigma> by simp
        hence "O y z" using O_def R by auto
        hence "(\<exists> x. F x \<and> O x y)" using z by simp
        thus "(\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))" by (metis O_def R T \<open>y \<^bold>\<le> z\<close> z)
      next 
        assume "(\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
        hence "y \<^bold>\<le> z" using z by (meson D_def SS)
        thus "y \<^bold>\<le> (\<sigma> v. F v)" using \<sigma> by simp
      qed
    qed
  qed

  text {* Continuing to follow the  proof from @{cite "pontow_note_2004"} pp. 204, we can prove
the Product Axiom proper:  *}

lemma (in GEM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
proof 
  assume "O x y"
  hence ez:  "(\<exists> z. (z \<^bold>\<le> x \<and> z \<^bold>\<le> y))" using O_def by simp
  hence "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (\<exists> v. (v \<^bold>\<le> x \<and> v \<^bold>\<le> y) \<and> O v w))" using FP by simp
  then obtain z where "(\<forall> w. O w z \<longleftrightarrow> (\<exists> v. (v \<^bold>\<le> x \<and> v \<^bold>\<le> y) \<and> O v w))"..
  hence \<sigma>zxy: "(\<sigma> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y) = z" using UGS by simp
  have gragra: "(\<forall> s. s \<^bold>\<le> (\<sigma> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y) \<longleftrightarrow>
(\<forall> w. w \<^bold>\<le> s \<longrightarrow> (\<exists> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y \<and> O v w)))" using PS ez by simp
  have "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"
  proof
    fix w
    show "w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"
      proof
        assume "w \<^bold>\<le> z"
        hence "w \<^bold>\<le> (\<sigma> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y)" using \<sigma>zxy by simp
        hence dadada: "(\<forall> t. t \<^bold>\<le> w \<longrightarrow> (\<exists> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y \<and> O v t))" using gragra by simp
        have "\<forall> t. t \<^bold>\<le> w \<longrightarrow> (O t x \<and> O t y)"
        proof
          fix t
          show "t \<^bold>\<le> w \<longrightarrow> (O t x \<and> O t y)"
            proof
              assume "t \<^bold>\<le> w"
              hence "(\<exists> v. v \<^bold>\<le> x \<and> v \<^bold>\<le> y \<and> O v t)" using dadada by simp
              thus "O t x \<and> O t y" using O_def T by blast
            qed
          qed
          thus "w \<^bold>\<le> x \<and> w \<^bold>\<le> y" using SS T D_def by meson
        next
          assume "w \<^bold>\<le> x \<and> w \<^bold>\<le> y"
          thus "w \<^bold>\<le> z" using O_def R \<sigma>zxy gragra by fastforce
        qed
      qed
      thus "(\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"..
    qed

(* Naming of sentences in this proof need to be tidied up. *)

text {* It follows that General Extensional Mereology is stronger than Closed Extensional Mereology *}

sublocale GEM \<subseteq> CEM using CEM.intro CM.intro CM_axioms_def EM_axioms M_axioms S T by blast

text {* Likewise, substituting @{text "x = x"} for @{text "F x"} in fusion allows the derivation of the 
existence of a universe: *}

lemma (in GM) selfidentity:
"(\<exists> x. x = x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y))"
  using F by fast
lemma (in GM) "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. O x y))" using selfidentity by simp
lemma (in GEM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z"
  using selfidentity by (metis D_def O_def SS)

text {* It follows that Classical Extensional Mereology is also stronger than Closed Extensional Mereology with Universe: *}

sublocale GEM \<subseteq> CEMU
proof
  show "\<exists>z. \<forall>x. x \<^bold>\<le> z" using U by simp
qed

text {* The existence of differences is also derivable in General Extensional Mereology. Like, the proof
of the product axiom, the proof of the existence of differences is quite involved. It can be found
in Pontow @{cite "pontow_note_2004"} p. 209. *}

lemma (in GM) FD: "(\<exists> x. x \<^bold>\<le> a \<and> \<not> O x b) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x \<^bold>\<le> a \<and> \<not> O x b) \<and> O x y))" using F solve_direct.

lemma (in GEM) D: "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))"
proof
  assume "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y)"
  hence "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (\<exists> v. (v \<^bold>\<le> x \<and> \<not> O v y) \<and> O v w))" using FD by simp
  then obtain \<Sigma> where \<Sigma>: "\<forall> w. O w \<Sigma> \<longleftrightarrow> (\<exists> v. (v \<^bold>\<le> x \<and> \<not> O v y) \<and> O v w)"..
  have "\<forall> w. w \<^bold>\<le> \<Sigma> \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)"
  proof
    fix w
    show "w \<^bold>\<le> \<Sigma> \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)"
      proof
        assume "w \<^bold>\<le> \<Sigma>"
        have "\<forall> z. z \<^bold>\<le> w \<longrightarrow> O z x"
        proof
          fix z
          show "z \<^bold>\<le> w \<longrightarrow> O z x"
            proof
              assume "z \<^bold>\<le> w"
              hence "\<exists> s0. (s0 \<^bold>\<le> x \<and> \<not> O s0 y) \<and> O s0 z"  using M.T M_axioms O_def R \<Sigma> \<open>w \<^bold>\<le> \<Sigma>\<close> by blast
              thus "O z x" using M.T M_axioms O_def by blast
            qed
          qed
          hence "w \<^bold>\<le> x" using SS D_def by blast
          have "\<forall> v. v \<^bold>\<le> w \<longrightarrow> \<not> v \<^bold>\<le> y" by (metis O_def M.T M_axioms \<Sigma> \<open>w \<^bold>\<le> \<Sigma>\<close>)
              hence "\<not> O w y" using O_def by simp
              thus "w \<^bold>\<le> x \<and> \<not> O w y" using \<open>w \<^bold>\<le> x\<close> by blast
            next
              assume "w \<^bold>\<le> x \<and> \<not> O w y"
              show "w \<^bold>\<le> \<Sigma>" by (meson D_def O_def R SS \<Sigma> \<open>w \<^bold>\<le> x \<and> \<not> O w y\<close>)
            qed
           qed
           thus "(\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))"..
         qed

section {* Atomism *}

text {* An atom is an individual with no proper parts: *}

definition (in M) A:: "i \<Rightarrow> bool" ("A")
  where "A x  \<equiv> \<not> (\<exists> y. y \<^bold>< x)" 

text {* Each theory discussed above can be augmented with an axiom stating that everything has
an atom as a part, viz. @{cite "casati_parts_1999"}, p. 48: *}

locale AM = M +
  assumes A: "\<forall> x. \<exists> y. A y \<and> y \<^bold>\<le> x" -- "atomicity"
locale AMM = AM + MM
locale AEM = AM + EM
locale ACM = AM + CM
locale ACEM = AM + CEM
locale AGM = AM + GM
locale AGEM = AM + GEM

text {* It follows in @{text "AEM"} that if something is not part of another, there is an atom
which is part of the former but not part of the later: *}

lemma (in AEM)
ASS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y))"
proof
  assume "\<not> x \<^bold>\<le> y"
  hence "(\<exists> w. w \<^bold>\<le> x \<and> D w y)" using SS by simp
  then obtain w where w: "w \<^bold>\<le> x \<and> D w y"..
  hence "\<exists> z. A z \<and> z \<^bold>\<le> w" using A by simp
  then obtain z where z: "A z \<and> z \<^bold>\<le> w"..
  hence "A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y)" by (meson D_def O_def T w)
  thus "\<exists> z. A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y)"..
qed

text {* Moreover, in Minimal Mereology this lemma entails both strong supplementation and atomism,
so it serves as an alternative characterisation of Atomistic Extensional Mereology: *}

lemma (in MM)
  assumes ASS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y))"
  shows SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" using D_def assms by blast

lemma (in M)
  assumes ASS: "\<forall> x. \<forall> y. \<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y))"
  shows A: "\<forall> x. \<exists> y. A y \<and> y \<^bold>\<le> x"
proof
  fix x
  show "\<exists> y. A y \<and> y \<^bold>\<le> x"
  proof cases
    assume "A x"
    hence "A x \<and> x \<^bold>\<le> x" using R by simp
    thus "\<exists> y. A y \<and> y \<^bold>\<le> x"..
  next
    assume "\<not> A x"
    hence "\<exists> y. y \<^bold>< x" using A_def by simp
    then obtain y where y: "y \<^bold>< x"..
    hence  "\<not> x \<^bold>\<le> y" using PP_def by simp
    hence "\<exists> z. A z \<and> (z \<^bold>\<le> x \<and> \<not> O z y)" using ASS by blast
    thus "\<exists> y. A y \<and> y \<^bold>\<le> x" by blast 
  qed
qed

text {* So the axiom of Atomistic Strong Supplementation could be used in place of the two axioms of
Atomicity and Strong Supplementation @{cite "casati_parts_1999"} *}

text {* For the same reason that the Product axiom and  Strong Supplementation do not follow from the 
Fusion Axiom in General Mereology, and so General Mereology is strictly weaker than Classical Extensional
Mereology, the Product Axiom and Strong Supplementation still do not follow from the Fusion Axiom in
Atomistic General Mereology, and so Atomistic General Mereology is also strictly weaker than Atomistic
Classical Extensional Mereology @{cite "pontow_note_2004"}, p. 206: *}

lemma (in AGM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" nitpick [user_axioms] oops
lemma (in AGM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" nitpick [user_axioms] oops

text {* Alternatively, each theory discussed above can be augmented with an axiom stating that there are no
atoms, viz.: *}

locale XAM = M +
  assumes XA: "\<not> (\<exists> x. A x)" -- "atomlessness"
locale XAMM = XAM + MM
locale XAEM = XAM + EM
locale XACM = XAM + CM
locale XACEM = XAM + CEM
locale XAGM = XAM + GM
locale XAGEM = XAM + GEM

text {* Pontow notes that the question of whether the Fusion Axiom entails the Product and
Strong Supplementation axioms in Atomless General Mereology is open @{cite "pontow_note_2004"}.
Nitpick does not find a countermodel (since an infinite countermodel is needed?) and sledgehammer
fails to find a proof, so this problem remains open for now:  *}

lemma (in XAGM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" oops
lemma (in XAGM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" oops

section {* Consistency *}

text {* I conclude by proving the consistency of all the theories mentioned. *}

lemma (in M)  "False" nitpick [show_all] oops
lemma (in MM)  "False" nitpick [show_all] oops
lemma (in EM)  "False" nitpick [show_all] oops
lemma (in CM)  "False" nitpick [show_all] oops
lemma (in CEM)  "False" nitpick [show_all] oops
lemma (in CMU) "False" nitpick [show_all] oops
lemma (in CEMU) "False" nitpick [show_all] oops
lemma (in GM) "False" nitpick [show_all] oops
lemma (in GEM) "False" nitpick [show_all] oops

end