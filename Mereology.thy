section {* Introduction *}

theory Mereology
imports Main
begin

text {* An ax is a whole composed of a handle and a blade. The handle and blade are parts of the ax.
The relation of the handle and the blade to the ax is known as \emph{parthood}, and the study of
parthood is known as \emph{mereology} (from the Greek word for part).*}

text {* In contemporary metaphysics, mereology is a paradigmatic example of the axiomatic method in
philosophy. The axiomatic nature of mereological theories make them an ideal target for exploration
using automatic methods, which is the purpose of this paper. *}

text {* In particular, this paper uses the interactive theorem prover Isabelle/HOL in order to present
an axiomatization of \emph{Classical Extensional Mereology}. The paper is based largely on the
presentation of Classical Extensional Mereology in ``Parts'' by Peter Simons @{cite "simons_parts:_1987"}
and ``Parts and Places'' by Roberto Casati and Achille Varzi @{cite "casati_parts_1999"}.*}

text {* I will focus in particular on three philosophical controversies concerning Classical
Extensional Mereology. The first is the issues which gives Classical Extensional Mereology it's
middle name, \emph{extensionality} itself. Roughly speaking, extensionality is the claim that
anythings composed of exactly the same things are identical. *}

text {* In the purely mereological context, extensionality is highly intuitive, and purported 
counterexamples to it seem strained. But when mereology is taken into modal and temporal contexts, 
extensionality is implicated at the origins of various paradoxes. As a result, many philosophers are
inclined to reject it. *}

text {* The second controversy concerns principles of \emph{closure}, which say when some things come
together to make a whole. The strongest closure principle is \emph{unrestricted composition}, according
to which, roughly speaking, \emph{any} things come together to make a whole. The mathematical elegance
linked to unrestricted composition is in part what makes it a \emph{classical} theory. *}

text {* The first section of the paper introduces Classical Extensional Mereology via six weaker subtheories:
Ground Mereology (M), Minimal Mereology (MM), Extensional Mereology (EM), Closure Mereology (CM), Closure Mereology
with Universe (CMU) and General Mereology (GM). Combinations of these subtheories mentioned are Closure
Extensional Mereology (CEM) and Closure Extensional Mereology with Universe (CEMU). The second section of
the paper verifies the theorems listed by Simons @{cite "simons_parts:_1987"}, pp. 38-41. The paper concludes by
verifying consistency of all theories mentioned. *}

section {* Theories *}

subsection {* Ground Mereology *}

text {* Ground Mereology (M) introduces parthood as a primitive relation amongst individuals.
It's assumed that parthood is a partial ordering relation @{cite "casati_parts_1999"}, p. 36:  *}

typedecl i -- "the type of individuals"

locale P =
  fixes P:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)

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
  where "x \<^bold>\<times> y \<equiv> THE z. \<forall> w. P w z \<longleftrightarrow> P w x \<and> P w y" -- "product or intersection"
definition u:: "i" ("u")
  where "u \<equiv> THE z. \<forall> w. P w z" -- "definition of the universe"
definition M:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<^bold>-" 51)
  where "x \<^bold>- y \<equiv> THE z. \<forall> w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y" -- "difference"
definition C:: "i \<Rightarrow> i" ("\<^bold>\<not>")
  where "\<^bold>\<not> x \<equiv> THE z. \<forall> w. P w z \<longleftrightarrow> \<not> O w x" -- "complement"

text {* And the operations of general sum and product @{cite casati_parts_1999}, p. 46:  *}

definition \<sigma>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<sigma>")
  where "\<sigma> F \<equiv> THE x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y)"
abbreviation \<sigma>x:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" [8] 9)
  where "\<sigma> x. F x \<equiv> \<sigma> F" --  "general sum or fusion of the Fs"
definition \<pi>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<pi>")
  where "\<pi> F \<equiv> \<sigma> x. \<forall> y. F y \<longrightarrow> x \<^bold>\<le> y" -- "general products @{cite casati_parts_1999}, p. 46"
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

locale R = P + assumes R: "x \<^bold>\<le> x" -- "reflexivity of parthood "
locale AS = P + assumes AS: "x \<^bold>\<le> y \<longrightarrow> y \<^bold>\<le> x \<longrightarrow> x = y" -- "antisymmetry of parthood"
locale T = P + assumes T: "x \<^bold>\<le> y \<longrightarrow> y \<^bold>\<le> z \<longrightarrow> x \<^bold>\<le> z" -- "transitivity of parthood"

locale M = R + AS + T

subsection {* Minimal Mereology *}

text {* Minimal mereology (MM) adds to ground mereology the axiom of weak supplementation: @{cite "casati_parts_1999"}, p. 39:    *}

locale MM = M +
  assumes WS: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)" -- "weak supplementation"

lemma (in M)  "(x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> D z x)) \<longleftrightarrow> (x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>\<le> y \<and> D z x))"
  by (metis AS D_def O_def PP_def R)

(* names "company" and "strong company" are from SEP *)

lemma (in MM)  SF1: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<noteq> x \<and> z \<^bold>< y)" by (metis WS D_def O_def R) -- "company"
lemma (in MM)  SF2: "x \<^bold>< y \<longrightarrow> (\<exists> z. z \<^bold>< y \<and> \<not> z \<^bold>\<le> x)" by (metis WS D_def O_def R) -- "strong company"

lemma (in MM) PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y" -- "proper parts principle"
  nitpick oops
lemma (in M) E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y" -- "extensionality"
  nitpick oops

subsection {* Extensional Mereology *}

text {* Extensional Mereology (EM) adds the axiom of strong supplementation @{cite "casati_parts_1999"}, p. 39: *}

locale EM = M +
  assumes SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" -- "strong supplementation"

text {*  Extensional Mereology (@{text "EM"} is so called because it entails extensionality: @{cite "casati_parts_1999"} p. 40: *}

lemma (in EM) PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y"
  by (metis SS D_def R O_def PP_def T)

lemma (in EM)
 E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y" -- "extensionality"
  by (metis R O_def D_def AS PP_def SS)

lemma (in M)
  assumes PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y"
  shows E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y"
  using PPP AS PP_def by blast

lemma (in MM) 
 assumes E: "(\<exists> z. z \<^bold>< x \<or> z \<^bold>< y) \<longrightarrow> (\<forall> z. z \<^bold>< x \<longleftrightarrow> z \<^bold>< y) \<longrightarrow> x = y"
 shows PPP: "\<exists> z. z \<^bold>< x \<Longrightarrow> \<forall> z. z \<^bold>< x \<longrightarrow> z \<^bold>\<le> y \<Longrightarrow> x \<^bold>\<le> y" 
  nitpick oops

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

  text {* Two alternative formulations of the strong supplementation axiom, which are equivalent given
transitivity are @{cite "pontnow_note_2004"} p. 198: *}

lemma (in P) "((\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y) \<longleftrightarrow> (\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y))"
  using D_def by blast

lemma (in M)
"((\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y) \<longleftrightarrow> (\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y))"
  by (metis O_def D_def R T)

lemma (in P) assumes SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
  shows "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  using D_def SS by blast

lemma (in R) assumes "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  shows "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y"
  using O_def R assms by blast

lemma (in T) assumes "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" 
  shows SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)"
  by (meson D_def O_def T assms)

lemma (in EM) "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" using SS D_def by blast
lemma (in EM) "(\<forall> z. O z x \<longrightarrow> O z y) \<longrightarrow> x \<^bold>\<le> y" by (metis SS T D_def O_def)

subsection {* Closure Mereology *}

text {* Closure Mereology adds to Ground Mereology the axioms of sum closure and product closure
 @{cite "casati_parts_1999"} p. 43: *}

locale CM = M +
  assumes SC: "U x y \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
-- "sum closure"
  assumes PC: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
-- "product closure"

text {* The product closure axiom and weak supplementation jointly entail strong supplementation
@{cite "simons_parts:_1987"}. The proof verified here is from @{cite "pontow_note_2004"} p. 200: *}

locale CMM = CM + MM

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
    then obtain z where "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"..
    hence "z \<^bold>< x" using PP_def R \<open>\<not> x \<^bold>\<le> y\<close> by auto
    hence "(\<exists> w. w \<^bold>< x \<and> D w z)" using WS by simp
    then obtain w where "w \<^bold>< x \<and> D w z"..
    hence "w \<^bold>\<le> x \<and> D w y" by (meson D_def O_def PP_def T \<open>\<forall>w. (w \<^bold>\<le> z) = (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)\<close>)
    thus "(\<exists> z. z \<^bold>\<le> x \<and> D z y)"..
  qed
qed

text {* Adding Extensional Mereology to Closed Mereology results in Closure Extensional Mereology
 @{cite "casati_parts_1999"} p. 43: *}

locale CEM = EM + CM

text {* Because Strong Supplementation is provable in Closed Minimal Mereology, it follows that
closed extensional mereology and closed minimal mereology is the same theory (reference?): *}

sublocale CEM \<subseteq> CMM by (simp add: CMM.intro CM_axioms MM_axioms)
sublocale CMM \<subseteq> CEM  by (simp add: CEM.intro CM_axioms EM.intro EM_axioms.intro M_axioms SS)

subsection {* Closure Mereology with Universe *}

text {* Closure Mereology with Universe (CMU) is obtained by adding  an axiom ensuring existence
of a universe @{cite "casati_parts_1999"} p. 44:  *}

locale CMU = CM +
  assumes U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" -- "universe"

text {* And adding Extensional Mereology to this theory results in
Closed Extensional Mereology with Universe @{text "CEMU"}: *}

locale CEMU = EM + CMU

text {* In Closure Extensional Mereology with Universe, it's possible to derive the existence of
unrestricted sums, since everything underlaps everything else: *}

lemma (in CEMU) EU: "U x y" using P.U_def U by auto -- "everything underlaps"
lemma (in CEMU) USC: "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))" using EU SC by simp
 -- "unrestricted sum closure"

text {* However, it's still not possible to derive the existence of differences:  *}

lemma (in CEMU) D: "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" oops

subsection {* General Mereology *}

text {* General Mereology is obtained from Ground Mereology by adding the axiom of fusion or
unrestricted composition @{cite "casati_parts_1999"} p. 46:  *}

locale GM = M +
  assumes F: "(\<exists> x. F x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
-- "fusion or unrestricted composition"

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

lemma (in GM) PC: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
  nitpick [show_all] oops

text {* It follows that General Mereology does not encompass Closure Mereology: *}

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

text {* But it's important to note that that doesn't mean there is a universe. If for example,
there is just an infinite ascending chain, then everything overlaps everything else, but there isn't
a particular thing which everything is a part of, since for anything in particular, the things above it
are not part of the chain: *}

lemma (in GM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" nitpick oops

  text {* The existence of difference is still not guaranteed either: *}

lemma (in GM) D:  "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" nitpick oops

subsection {* General Minimal Mereology *}

text {* And hence that General Extensional Mereology is stronger than Closure Extensional Mereology
@{cite "casati_parts_1999"} p. 46. *}


  text {* It's frequently claimed that in General Mereology, strong supplementation is derivable from
weak supplementation, and so the combination of Minimal Mereology with General Mereology results in the
same theory as the combination of Extensional Mereology with Minimal Mereology (References to Simons,
Casati and Varzi and Varzi?). But this is not true (pontow). Call the combination of General Mereology
with weak supplementation General Minimal Mereology, or @{term "GMM"}: *}

locale GMM = MM + GM -- "General Minimal Mereology"

lemma (in GMM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" nitpick oops

  text {* Nor can product closure be derived in minimal mereology (if it could, then as we saw
earlier, strong supplementation could be derived from it *}


lemma (in GMM) PC: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" nitpick [show_all] oops

  text {* Nor can the existence of a universe or differences be proved in General Minimal Mereology *}

lemma (in GMM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z" nitpick oops
lemma (in GMM) D: "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" nitpick oops

subsection {* Classical Extensional Mereology *}

text {* Classical Extensional Mereology @{text "GEM"} is simply Extensional Mereology combined
with General Mereology  @{cite "casati_parts_1999"} p. 46: *}

locale GEM = EM + GM

text {* The presence of strong supplementation in Classical Extensional Mereology enables the derivation of 
product closure from fusion: *}

lemma (in GM) FP: "(\<exists> z. (z \<^bold>\<le> a \<and> z \<^bold>\<le> b)) \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (\<exists> x. (x \<^bold>\<le> a \<and> x \<^bold>\<le> b) \<and> O x w))"
  using F solve_direct.

lemma (in EM) atothesum:
  assumes asum: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
  shows thesum: "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z"
proof (rule the_equality)
  show "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using asum.
  show "\<And>v. \<forall>y. O y v = (\<exists>x. F x \<and> O x y) \<Longrightarrow> v = z"  by (metis SS AS D_def O_def R asum)
qed

lemma (in EM) UGS: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) \<longrightarrow> (\<sigma> x. F x) = z"
proof
  assume "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
  hence "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z" using atothesum by simp
  thus "(\<sigma> v. F v) = z" using \<sigma>_def by blast
qed

text {* Following proof from @{cite "pontow_note_2004"} pp. 202-3  *}

lemma (in GEM) PS: "(\<exists> x. F x) \<longrightarrow> (\<forall> y. y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w)))"
proof
  assume "(\<exists> x. F x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence z\<sigma>: "(\<sigma> v. F v) = z " using UGS by simp
  show "\<forall> y. y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
  proof
    fix y
    show "y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
      proof
        assume "y \<^bold>\<le> (\<sigma> v. F v)"
        hence "y \<^bold>\<le> z" using z\<sigma> by simp
        hence "O y z" using O_def R by auto
        hence "(\<exists> x. F x \<and> O x y)" using z by simp
        thus "(\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))" by (metis P.O_def R T \<open>y \<^bold>\<le> z\<close> z)
      next 
        assume "(\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
        hence "y \<^bold>\<le> z" using z by (meson D_def SS)
        thus "y \<^bold>\<le> (\<sigma> v. F v)" using z\<sigma> by simp
      qed
    qed
  qed

text {* Following proof from @{cite "pontow_note_2004"} pp. 204  *}

lemma (in GEM) PC: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
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
          thus "w \<^bold>\<le> z" using P.O_def R \<sigma>zxy gragra by fastforce
        qed
      qed
      thus "(\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"..
    qed

(*  "(\<exists> x. F x) \<longrightarrow> (\<forall> y. y \<^bold>\<le> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. F v \<and> O v w)))" *)

text {* Likewise, substituting @{text "x = x"} for @{text "F x"} in fusion allows the derivation of the 
existence of a universe: *}

lemma (in GM) selfidentity:
"(\<exists> x. x = x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y))"
  using F by fast
lemma (in GM) "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. O x y))" using selfidentity by simp
lemma (in GEM) U: "\<exists> z. \<forall> x. x \<^bold>\<le> z"
  using selfidentity by (metis D_def O_def SS)

text {* It follows that Classical Extensional Mereology is stronger than Closed Extensional Mereology with Universe: *}

sublocale GEM \<subseteq> CEMU
proof
  show "\<And>x y. U x y \<longrightarrow> (\<exists>z. \<forall>w. O w z = (O w x \<or> O w y))" using S by simp
  show "\<And>x y. O x y \<longrightarrow> (\<exists>z. \<forall>w. (w \<^bold>\<le> z) = (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
    using PC by simp
  show "\<exists>z. \<forall>x. x \<^bold>\<le> z" using U by simp
qed

text {* The existence of differences is also derivable in General Extensional Mereology Pontow p. 209 *}


lemma (in GM) FD: "(\<exists> x. x \<^bold>\<le> a \<and> \<not> O x b) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x \<^bold>\<le> a \<and> \<not> O x b) \<and> O x y))" using F solve_direct.

lemma (in EM) SD: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> w. (w \<^bold>\<le> a \<and> \<not> O w b) \<and> O w y)) \<longrightarrow> (\<sigma> w. w \<^bold>\<le> a \<and> \<not> O w b) = z" using UGS solve_direct.


lemma (in GEM) ugly: "(\<exists> x. x \<^bold>\<le> a \<and> \<not> O x b) \<longrightarrow> (\<forall> y. y \<^bold>\<le> (\<sigma> v. v \<^bold>\<le> a \<and> \<not> O v b)
\<longleftrightarrow> (\<forall> w. w \<^bold>\<le> y \<longrightarrow> (\<exists> v. v \<^bold>\<le> a \<and> \<not> O v b \<and> O v w)))" using PS by simp

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
              hence "\<exists> s0. (s0 \<^bold>\<le> x \<and> \<not> O s0 y) \<and> O s0 z" by (metis P.O_def R T.T T_axioms \<Sigma> \<open>w \<^bold>\<le> \<Sigma>\<close>)
              thus "O z x" using O_def T.T T_axioms by blast
            qed
          qed
          hence "w \<^bold>\<le> x" using SS D_def by blast
          have "\<forall> v. v \<^bold>\<le> w \<longrightarrow> \<not> v \<^bold>\<le> y" by (metis P.O_def T.T T_axioms \<Sigma> \<open>w \<^bold>\<le> \<Sigma>\<close>)
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

definition (in P) A:: "i \<Rightarrow> bool" ("A")
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

text {* Carsten Pontow notes that the question of whether the Fusion Axiom entails the Product and
Strong Supplementation axioms in Atomless General Mereology is open @{cite "pontow_note_2004"}. Nitpick fails to find a countermodel
and sledgehammer fails to find a proof, so this problem remains open for now:  *}

(*
lemma (in XAGM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" nitpick [user_axioms] oops
lemma (in XAGM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" nitpick [user_axioms] oops

lemma (in XAGM) T: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" sledgehammer  oops
lemma (in XAGM) SS: "\<not> x \<^bold>\<le> y \<longrightarrow> (\<exists> z. z \<^bold>\<le> x \<and> D z y)" sledgehammer oops
*)


section {* Theorems *}

text {* The remainder of the paper verifies the theorems list by Simons @{cite "simons_parts:_1987"}, pp. 38-41.
The numbering of theorems is taken from him, except that his T2, T3 and T4 are our axioms of ground mereology,
and his A1 and A2 are thus theorems for us. I also follow Simons division of the theorems into categories
according to their most important relation or operator. *}

subsection {* Proper Parthood *}

lemma (in M) T1: "\<not> x \<^bold>< x"
  by (simp add: PP_def) -- "irreflexivity of proper parthood"
lemma (in M) A1: "x \<^bold>< y \<longrightarrow> \<not> y \<^bold>< x"
  by (simp add: PP_def) -- "asymmetry of proper parthood"
lemma (in M) A2: "x \<^bold>< y \<longrightarrow> y \<^bold>< z \<longrightarrow> x \<^bold>< z"
  using PP_def T by blast -- "transitivity of proper parthood"

subsection {* Parthood *}

lemma (in M) T3: "x = y \<longleftrightarrow> x \<^bold>\<le> y \<and> y \<^bold>\<le> x" using AS R by blast
lemma (in M) T5: "x \<^bold>\<le> y \<and> y \<^bold>< z \<longrightarrow> x \<^bold>< z" using PP_def T by blast
lemma (in M) T6: "x \<^bold>< y \<and> y \<^bold>\<le> z \<longrightarrow> x \<^bold>< z" using PP_def T by blast
lemma (in M) T7: "x = y \<longleftrightarrow> (\<forall> z. z \<^bold>\<le> x \<longleftrightarrow> z \<^bold>\<le> y)" using AS R by auto
lemma (in M) T8: "x = y \<longleftrightarrow> (\<forall> z. x \<^bold>\<le> z \<longleftrightarrow> y \<^bold>\<le> z)" using AS R by auto

subsection {*Overlap*}

lemma (in M) T9: "O x x" using O_def R by blast -- "reflexivity of overlap"
lemma (in M) T10: "O x y \<longrightarrow> O y x"
  using O_def by blast -- "symmetry of overlap"
lemma (in M) T11: "x \<^bold>\<le> y \<longrightarrow> O x y"
  using O_def R by auto -- "parthood implies overlap"
lemma (in M) T12: "x \<^bold>\<le> y \<and> O x z \<longrightarrow> O y z" using O_def T by blast
lemma (in EM) T13: "x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y)"
  by (meson SS T T11 D_def)
lemma (in M) T14: "(\<forall> z. z \<^bold>\<le> x \<longrightarrow> O z y) \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  using O_def T11 T12 by blast
lemma (in EM) T15: "x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  using T13 T14 by blast
lemma (in EM) T16: "x = y \<longleftrightarrow> (\<forall> z. O x z \<longleftrightarrow> O y z)"
  by (meson AS T10 T11 T13)

subsection {* Disjointness *}

lemma (in M) T17: "\<not> D x x" using D_def O_def R
  by blast --  "irreflexivity of disjointness"
lemma (in M) T18: "D x y \<longrightarrow> D y x"
  using D_def O_def by auto -- "symmetry of disjointness"
lemma (in M) T19: "x \<^bold>\<le> y \<and> D y z \<longrightarrow> D x z"
  using D_def O_def M_axioms T by presburger
lemma (in EM) T20: "x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> D z x)"
  by (metis D_def O_def R SS T)
lemma (in EM) T21: "x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> \<not> z \<^bold>\<le> x)"
  by (metis D_def T O_def R SS)
lemma (in EM) T22: "x = y \<longleftrightarrow> (\<forall> z. D z x \<longleftrightarrow> D z y)" using AS T20 by blast

subsection {* Products *}

text {* The proofs of T23 and T24 are slightly indirect. T23a is also used in the next section to
prove T31. *}

lemma (in EM) T23a: "(THE z. \<forall> w. P w z \<longleftrightarrow> P w x \<and> P w x) = x"
proof (rule the_equality)
  show "\<forall> w. w \<^bold>\<le> x \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> x)" by simp
  show "\<And> z. \<forall>w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> x) \<Longrightarrow> z = x" using AS R by blast
qed
lemma (in M) T23b: "x \<^bold>\<times> x = (THE z. \<forall> w. P w z \<longleftrightarrow> P w x \<and> P w x)" using T_def by simp
lemma (in EM) T23: "x = x \<^bold>\<times> x" using T23a T23b by simp
lemma (in M) T24a: "(THE z. \<forall> w. P w z \<longleftrightarrow> P w x \<and> P w y) = (THE z. \<forall> w. P w z \<longleftrightarrow> P w y \<and> P w x)" by metis
lemma (in M) T24: "x \<^bold>\<times> y = y \<^bold>\<times> x" using T_def T24a by simp  -- "intersection is commutative"
lemma (in CEM) T25: "O x y \<longrightarrow> x \<^bold>\<times> y \<^bold>\<le> x \<and> x \<^bold>\<times> y \<^bold>\<le> y"
proof
  assume "O x y"
  hence "\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using PC by simp
  then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"..
  hence "(THE v. \<forall> w. P w v \<longleftrightarrow> P w x \<and> P w y) = z"
  proof (rule the_equality)
    show "\<And>v. \<forall>w. w \<^bold>\<le> v \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y) \<Longrightarrow> v = z" using z AS R by blast
  qed
  hence "z = x \<^bold>\<times> y" using T_def by simp
  hence "x \<^bold>\<times> y \<^bold>\<le> z" using R by simp
  thus "x \<^bold>\<times> y \<^bold>\<le> x \<and> x \<^bold>\<times> y \<^bold>\<le> y" using z by simp
qed

lemma (in CEM) T26: "O x y \<and> z \<^bold>\<le> x \<^bold>\<times> y \<longrightarrow> z \<^bold>\<le> x \<and> z \<^bold>\<le> y" using T T25 by blast
lemma (in CEM) T27: "x \<^bold>\<le> y \<longrightarrow> x \<^bold>\<times> y = x"
proof
  assume "x \<^bold>\<le> y"
  hence "O x y" using T11 by simp
  hence "\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using PC by simp
  then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"..
  hence "(THE v. \<forall> w. P w v \<longleftrightarrow> P w x \<and> P w y) = z"
  proof (rule the_equality)
    show "\<And>v. \<forall>w. w \<^bold>\<le> v \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y) \<Longrightarrow> v = z" using z AS R by blast
  qed
  hence "z = x \<^bold>\<times> y" using T_def by simp
  hence "\<forall> w. w \<^bold>\<le> x \<^bold>\<times> y \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using z by simp
  hence "x \<^bold>\<le> x \<^bold>\<times> y \<longleftrightarrow> (x \<^bold>\<le> x \<and> x \<^bold>\<le> y)"..
  hence "x \<^bold>\<le> x \<^bold>\<times> y" using R \<open>x \<^bold>\<le> y\<close> by blast
  thus "x \<^bold>\<times> y = x" using AS T25 \<open>O x y\<close> by simp
qed

lemma (in CEM) T28: "O x y \<and> x = x \<^bold>\<times> y \<longrightarrow> x \<^bold>\<le> y" using T25 by force
lemma (in CEM) T29: "x \<noteq> y \<and> O x y \<longrightarrow> x \<^bold>\<times> y \<^bold>< x \<or> x \<^bold>\<times> y \<^bold>< y" by (metis AS PP_def T25)

lemma (in CEM) T30:
"(\<exists> w. w \<^bold>\<le> x \<and> w \<^bold>\<le> y \<and> w \<^bold>\<le> z) \<longrightarrow> x \<^bold>\<times> (y \<^bold>\<times> z) = (x \<^bold>\<times> y) \<^bold>\<times> z"
proof
  assume w: "(\<exists> w. w \<^bold>\<le> x \<and> w \<^bold>\<le> y \<and> w \<^bold>\<le> z)"
  hence "O y z" using O_def by auto
  hence "\<exists> v. \<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)" using PC by simp
  then obtain v where v: "\<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)"..
  hence THEv: "(THE v. \<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)) = v"
  proof (rule the_equality)
    show "\<And>va. \<forall>s. (s \<^bold>\<le> va) = (s \<^bold>\<le> y \<and> s \<^bold>\<le> z) \<Longrightarrow> va = v"
      using AS R v by blast
  qed
  hence "O x v" by (simp add: O_def w v)
  hence "\<exists> t. \<forall> w. P w t \<longleftrightarrow> (P w x \<and> P w v)" using PC by simp
  hence "\<exists> t. \<forall> w. P w t \<longleftrightarrow> (P w x \<and> P w (THE v. \<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)))" using THEv by blast
  then obtain t where t: "\<forall> w. P w t \<longleftrightarrow> (P w x \<and> P w (THE v. \<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)))"..
  hence "(THE t. \<forall> w. P w t \<longleftrightarrow> (P w x \<and> P w (THE v. \<forall> s. P s v \<longleftrightarrow>  (P s y \<and> P s z)))) = t"
  proof (rule the_equality)
    show "\<And>ta. \<forall>w. (w \<^bold>\<le> ta) = (w \<^bold>\<le> x \<and> w \<^bold>\<le> (THE v. \<forall>s. (s \<^bold>\<le> v) = (s \<^bold>\<le> y \<and> s \<^bold>\<le> z))) \<Longrightarrow> ta = t" using AS R t by blast
  qed
  hence xyzt: "(x \<^bold>\<times> (y \<^bold>\<times> z)) = t" using T_def by simp
  have "O x y" using w O_def by auto
  hence "\<exists> j. \<forall> s. P s j \<longleftrightarrow> (P s x \<and> P s y)" using PC by simp
  then obtain j where j: "\<forall> s. P s j \<longleftrightarrow> (P s x \<and> P s y)"..
  hence THEj: "(THE j. \<forall> s. P s j \<longleftrightarrow> (P s x \<and> P s y)) = j"
  proof (rule the_equality)
    show "\<And>ja. \<forall>s. (s \<^bold>\<le> ja) = (s \<^bold>\<le> x \<and> s \<^bold>\<le> y) \<Longrightarrow> ja = j" using AS R j by blast
  qed
  hence "O j z" using w j O_def by simp
  hence "\<exists> k. \<forall> w. P w k \<longleftrightarrow> (P w j \<and> P w z)" using PC by simp
  hence "\<exists> k. \<forall> w. P w k \<longleftrightarrow> (P w (THE v. \<forall> s. P s v \<longleftrightarrow> (P s x \<and> P s y)) \<and> P w z)" using THEj by simp
  then obtain k where k: "\<forall> w. P w k \<longleftrightarrow> (P w (THE v. \<forall> s. P s v \<longleftrightarrow> (P s x \<and> P s y)) \<and> P w z)"..
  hence THEk: "(THE k. \<forall> w. P w k \<longleftrightarrow> (P w (THE v. \<forall> s. P s v \<longleftrightarrow> (P s x \<and> P s y)) \<and> P w z)) = k"
  proof (rule the_equality)
    show "\<And>ka. \<forall>w. (w \<^bold>\<le> ka) = (w \<^bold>\<le> (THE v. \<forall>s. (s \<^bold>\<le> v) = (s \<^bold>\<le> x \<and> s \<^bold>\<le> y)) \<and> w \<^bold>\<le> z) \<Longrightarrow> ka = k" using AS R k by blast
  qed
  hence xyzk: "(x \<^bold>\<times> y) \<^bold>\<times> z = k" using T_def by simp
  have "t = k" by (metis AS R THEj THEv j v t k)
  thus "x \<^bold>\<times> (y \<^bold>\<times> z) = (x \<^bold>\<times> y) \<^bold>\<times> z" using xyzt xyzk by simp
qed

subsection {* Sums *}

lemma (in M) T31a: "x \<^bold>+ x = (THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w x)"
  using S_def by simp
lemma (in EM) T31b: "(THE z. \<forall> w. O w z \<longleftrightarrow>  (O w x \<or> O w x)) = x"
proof (rule the_equality)
  show "\<forall>w. O w x = (O w x \<or> O w x)" by simp
  show "\<And>z. \<forall>w. O w z = (O w x \<or> O w x) \<Longrightarrow> z = x" by (simp add: AS T15)
qed
lemma (in EM) T31: "x = x \<^bold>+ x" using T31a T31b by auto
lemma (in M)  T32a:
"(THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y) = (THE z. \<forall> w. O w z \<longleftrightarrow> O w y \<or> O w x)"
  by metis
lemma (in M) T32: "x \<^bold>+ y = y \<^bold>+ x"
  using S_def T32a by simp -- "summation is commutative"

lemma (in CEMU) USCP: "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)"
proof -
have "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))" using USC.
  then obtain z where z: "\<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y)"..
  hence "(THE z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y)) = z"
  proof (rule the_equality)
    show "\<And>za. \<forall>w. O w za = (O w x \<or> O w y) \<Longrightarrow> za = z" by (simp add: AS T15 z)
  qed
  hence "x \<^bold>+ y = z" using S_def by simp
  thus "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)" using z by simp
qed

lemma (in CEMU) T33: "x \<^bold>+ (y \<^bold>+ z) = (x \<^bold>+ y) \<^bold>+ z"
proof -
  have "\<forall> w. O w (y \<^bold>+ z) \<longleftrightarrow> (O w y \<or> O w z)" using USCP.
  hence left: "\<forall> w. O w (x \<^bold>+ (y \<^bold>+ z)) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)" using USCP by simp
  have "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)" using USCP.
  hence right:  "\<forall> w. O w ((x \<^bold>+ y) \<^bold>+ z) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)" using USCP by simp
  hence "(\<forall> w. O (x \<^bold>+ (y \<^bold>+ z)) w \<longleftrightarrow> O ((x \<^bold>+ y) \<^bold>+ z) w)" using left T10 by blast
  thus "x \<^bold>+ (y \<^bold>+ z) = (x \<^bold>+ y) \<^bold>+ z" using T16 by simp
qed

lemma (in CEMU) T34: "x \<^bold>\<le> x \<^bold>+ y" 
proof -
  have "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)" using USCP.
  hence "\<forall> w. O w x \<longrightarrow> O w (x \<^bold>+ y)" by simp
  hence "\<forall> w. P w x \<longrightarrow> O w (x \<^bold>+ y)" using T11 by blast
  thus "x \<^bold>\<le> (x \<^bold>+ y)" using T13 by blast
qed

lemma (in CEMU) T35: "y \<^bold>\<le> x \<^bold>+ y" using T32 T34 by fastforce
lemma (in CEMU) T36: "x \<^bold>+ y \<^bold>\<le> z \<longleftrightarrow> x \<^bold>\<le> z \<and> y \<^bold>\<le> z"
proof
  assume "x \<^bold>+ y \<^bold>\<le> z"
  thus "x \<^bold>\<le> z \<and> y \<^bold>\<le> z"using T T34 T35 by blast
next
  assume "x \<^bold>\<le> z \<and> y \<^bold>\<le> z"
  have "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)" using USCP.
  thus "x \<^bold>+ y \<^bold>\<le> z" using EM.T15 EM_axioms \<open>x \<^bold>\<le> z \<and> y \<^bold>\<le> z\<close> by fastforce
qed

lemma (in CEMU) T37: "D x y \<longrightarrow> x \<^bold>< x \<^bold>+ y \<and> y \<^bold>< x \<^bold>+ y"  by (metis D_def PP_def T11 T18 T34 T35 T36)
lemma (in CEMU) T38: "\<not> x \<^bold>\<le> y \<longrightarrow> y \<^bold>< x \<^bold>+ y" using PP_def T T34 T35 by blast
lemma (in CEMU) T39: "x \<noteq> y \<longleftrightarrow> x \<^bold>< x \<^bold>+ y \<or> y \<^bold>< x \<^bold>+ y"  by (metis AS PP_def T31 T35 T38)
lemma (in CEMU) T40: "x = x \<^bold>+ y \<longleftrightarrow> y \<^bold>\<le> x" by (metis AS R T36)
lemma (in CEMU) T41: "(x \<^bold>\<le> y \<^bold>+ z \<and> D x z) \<longrightarrow> x \<^bold>\<le> y"
proof
  assume "x \<^bold>\<le> y \<^bold>+ z \<and> D x z"
  hence "x \<^bold>\<le> y \<^bold>+ z"..
  have  "\<forall> w. O w (y \<^bold>+ z) \<longleftrightarrow> O w y \<or> O w z" using USCP.
  hence "\<forall> w. w \<^bold>\<le> (y \<^bold>+ z) \<longrightarrow> O w y \<or> O w z" using T11 by blast
  hence "\<forall> w. w \<^bold>\<le> x \<longrightarrow> O w y \<or> O w z" using T \<open>x \<^bold>\<le> y \<^bold>+ z\<close> by blast
  hence "\<forall> w. w \<^bold>\<le> x \<longrightarrow> O w y" using D_def T12 \<open>x \<^bold>\<le> y \<^bold>+ z \<and> D x z\<close> by blast
  thus "x \<^bold>\<le> y" using T13 by blast
qed

lemma (in CEMU) T42: "x \<^bold>< y \<and> D y z \<longrightarrow> x \<^bold>+ z \<^bold>< y \<^bold>+ z"
  by (metis M.T3 M_axioms PP_def T34 T36 T41)

subsection {* Difference *}

lemma (in GEM) T43a:  "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y) \<longrightarrow> (\<forall> w. w \<^bold>\<le> (x \<^bold>- y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))"
proof
  assume "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y)"
  hence "(\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y))" using D by simp
  then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)"..
  hence "(THE z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)) = z"
  proof (rule the_equality)
    show "\<And>za. \<forall>w. (w \<^bold>\<le> za) = (w \<^bold>\<le> x \<and> \<not> O w y) \<Longrightarrow> za = z" using AS R z by blast
  qed
  hence "(x \<^bold>- y) = z" using M_def by simp
  thus "\<forall> w. w \<^bold>\<le> (x \<^bold>- y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)" using z by simp
qed

lemma (in GEM) T43: "(O x y \<and> \<not> x \<^bold>\<le> y) \<longrightarrow> (x \<^bold>- y) \<^bold>< x"
proof
  assume "O x y \<and> \<not> x \<^bold>\<le> y"
  hence "(\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y)" using T13 by blast
  hence "\<forall> w. w \<^bold>\<le> (x \<^bold>- y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)" using T43a by simp
  thus "(x \<^bold>- y) \<^bold>< x" using PP_def R \<open>O x y \<and> \<not> x \<^bold>\<le> y\<close> by auto
qed

lemma (in GEM) T44: "x \<^bold>< y \<longrightarrow> y \<^bold>- x \<^bold>< y" using PP_def T10 T11 T43 by blast

lemma (in GEM) T45: "D x y \<longrightarrow> y \<^bold>- x = y"
proof
  assume "D x y"
  hence "(\<exists> w. w \<^bold>\<le> y \<and> \<not> O w x)" using D_def R T10 by blast
  hence "\<forall> w. w \<^bold>\<le> (y \<^bold>- x) \<longleftrightarrow> (w \<^bold>\<le> y \<and> \<not> O w x)" using T43a by simp
  thus "y \<^bold>- x = y" using AS D_def R T10 \<open>D x y\<close> by blast
qed

lemma (in GEM) T46: "\<not> y \<^bold>\<le> x \<and> y \<^bold>- x = y \<longrightarrow> D x y" using P.D_def T1 T10 T43 by fastforce

lemma (in GEM) T47: "D x y \<longrightarrow> (x \<^bold>+ y) \<^bold>- x = y"
proof
  assume "D x y"
  hence  "(\<exists> w. w \<^bold>\<le> (x \<^bold>+ y) \<and> \<not> O w x)" using P.D_def T10 T35 by blast
  hence "(\<forall> w. w \<^bold>\<le> ((x \<^bold>+ y) \<^bold>- x) \<longleftrightarrow> (w \<^bold>\<le> (x \<^bold>+ y) \<and> \<not> O w x))" using T43a by simp
  thus "(x \<^bold>+ y) \<^bold>- x = y" by (metis AS M.T32 M_axioms P.D_def R T18 T35 T41 \<open>D x y\<close>)
qed

lemma (in GEM) T48: "x \<^bold>< y \<longrightarrow> x \<^bold>+ (y \<^bold>- x) = y"
proof
  assume "x \<^bold>< y"
  hence  "(\<exists> w. w \<^bold>\<le> y \<and> \<not> O w x)" using PP_def T13 by blast
  hence "\<forall> w. w \<^bold>\<le> (y \<^bold>- x) \<longleftrightarrow> (w \<^bold>\<le> y \<and> \<not> O w x)" using T43a by simp
  have  "\<forall> w. O w (x \<^bold>+ (y \<^bold>- x)) \<longleftrightarrow> O w x \<or> O w (y \<^bold>- x)" using USCP.
  have "(THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w (y \<^bold>- x)) = y"
  proof (rule the_equality)
    show "\<forall>w. O w y = (O w x \<or> O w (y \<^bold>- x))"
      by (smt P.O_def PP_def T15 \<open>\<forall>w. (w \<^bold>\<le> y \<^bold>- x) = (w \<^bold>\<le> y \<and> \<not> O w x)\<close> \<open>x \<^bold>< y\<close>)
    show "\<And>z. \<forall>w. O w z = (O w x \<or> O w (y \<^bold>- x)) \<Longrightarrow> z = y"
      by (meson AS T11 T13 \<open>\<forall>w. O w y = (O w x \<or> O w (y \<^bold>- x))\<close>)
  qed
  thus "x \<^bold>+ (y \<^bold>- x) = y" using S_def by simp
qed

lemma (in GEM) PCP: "O x y \<longrightarrow> (\<forall> w. w \<^bold>\<le> (x \<^bold>\<times> y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))"
proof
  assume "O x y"
  hence "\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using PC by simp
  then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)"..
  hence "(THE z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)) = z"
  proof (rule the_equality)
    show "\<And>za. \<forall>w. (w \<^bold>\<le> za) = (w \<^bold>\<le> x \<and> w \<^bold>\<le> y) \<Longrightarrow> za = z" by (metis R T32 T40 z)
  qed
  hence "x \<^bold>\<times> y = z" using T_def by simp
  thus "(\<forall> w. w \<^bold>\<le> (x \<^bold>\<times> y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" using z by simp
qed

lemma (in GEM) T49: "O x y \<and> \<not> x \<^bold>\<le> y \<longrightarrow> x \<^bold>- (x \<^bold>\<times> y) = x \<^bold>- y"
proof
  assume "O x y \<and> \<not> x \<^bold>\<le> y"
  hence "\<exists> w. w \<^bold>\<le> x \<and> \<not> O w y" using T13 by blast
  hence right: "\<forall> w. w \<^bold>\<le> (x \<^bold>- y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w y)" using T43a by simp
  have "O x y" using \<open>O x y \<and> \<not> x \<^bold>\<le> y\<close>..
  hence "\<forall> w. w \<^bold>\<le> (x \<^bold>\<times> y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)" using PCP by simp
  hence "\<exists> w. w \<^bold>\<le> x \<and> \<not> O w (x \<^bold>\<times> y)" by (meson T13 \<open>O x y \<and> \<not> x \<^bold>\<le> y\<close>)
  hence left: "\<forall> w. w \<^bold>\<le> (x \<^bold>- (x \<^bold>\<times> y)) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w (x \<^bold>\<times> y))" using T43a by simp 
  hence "\<forall> w. w \<^bold>\<le> (x \<^bold>- (x \<^bold>\<times> y)) \<longleftrightarrow> w \<^bold>\<le> (x \<^bold>- y)"
    by (metis PCP T T11 T15 \<open>\<forall>w. (w \<^bold>\<le> x \<^bold>\<times> y) = (w \<^bold>\<le> x \<and> w \<^bold>\<le> y)\<close> right)
  thus "x \<^bold>- (x \<^bold>\<times> y) = x \<^bold>- y" using AS R by blast
qed
  
lemma (in GEM) T50: "\<not> x \<^bold>\<le> z \<longrightarrow> x \<^bold>\<le> y \<longrightarrow> x \<^bold>- z \<^bold>\<le> y \<^bold>- z"
proof
  assume "\<not> x \<^bold>\<le> z"
  hence "\<exists> w. w \<^bold>\<le> x \<and> \<not> O w z" using T13 by blast
  hence left: "(\<forall> w. w \<^bold>\<le> (x \<^bold>- z) \<longleftrightarrow> (w \<^bold>\<le> x \<and> \<not> O w z))" using T43a by simp
  show "x \<^bold>\<le> y \<longrightarrow> x \<^bold>- z \<^bold>\<le> y \<^bold>- z"
  proof
    assume "x \<^bold>\<le> y"
    hence "\<exists> w. w \<^bold>\<le> y \<and> \<not> O w z" by (meson left R T13)
    hence right: "(\<forall> w. w \<^bold>\<le> (y \<^bold>- z) \<longleftrightarrow> (w \<^bold>\<le> y \<and> \<not> O w z))" using T43a by simp
    hence "\<forall> w. w \<^bold>\<le> (x \<^bold>- z) \<longrightarrow> w \<^bold>\<le> (y \<^bold>- z)" using T \<open>x \<^bold>\<le> y\<close> left by blast
    thus "x \<^bold>- z \<^bold>\<le> y \<^bold>- z" using R by auto
  qed
qed

subsection {* Universe *}


lemma (in CEMU) T51a: "\<forall> x. x \<^bold>\<le> u"
proof -
  have "\<exists> z. \<forall> x. x \<^bold>\<le> z" using U.
  then obtain z where z: "\<forall> x. x \<^bold>\<le> z"..
  hence "(THE z. \<forall> x. x \<^bold>\<le> z) = z" using AS by blast
  thus "\<forall> x. x \<^bold>\<le> u" using z u_def by simp
qed

lemma (in CEMU)  T51: "u \<^bold>\<le> x \<longrightarrow> x = u" using T51a AS by simp

subsection {* Complement *}

lemma (in GEM) CC: "(\<exists> w. \<not> O w x) \<longrightarrow> (\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> \<not> O w x)" using D T51a by meson

lemma (in GEM) CCP: "(\<exists> w. \<not> O w x) \<longrightarrow> (\<forall> w. w \<^bold>\<le> (\<^bold>\<not> x) \<longleftrightarrow> \<not> O w x)"
proof
  assume "\<exists> w. \<not> O w x"
  hence "(\<exists> z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> \<not> O w x)" using CC by simp
  then obtain z where z: "\<forall> w. w \<^bold>\<le> z \<longleftrightarrow> \<not> O w x"..
  hence "(THE z. \<forall> w. w \<^bold>\<le> z \<longleftrightarrow> \<not> O w x) = z"
  proof (rule the_equality)
    show "\<And>za. \<forall>w. (w \<^bold>\<le> za) = (\<not> O w x) \<Longrightarrow> za = z" using AS R z by blast
  qed
  thus "\<forall> w. w \<^bold>\<le> (\<^bold>\<not> x) \<longleftrightarrow> \<not> O w x" using z C_def by simp
qed

lemma (in GEM) T52: "(\<exists>! z. \<forall> w. P w z \<longleftrightarrow> \<not> O w x) \<longleftrightarrow> x \<noteq> u"
proof
  assume  "(\<exists>! z. \<forall> w. P w z \<longleftrightarrow> \<not> O w x)"
  thus "x \<noteq> u" by (meson R T11 T51a)
next
  assume "x \<noteq> u"
  hence "\<exists> w. \<not> O w x" using T15 T51 by blast
  hence "\<exists> z. \<forall> w. P w z \<longleftrightarrow> \<not> O w x" using CC by simp
  thus "\<exists>! z. \<forall> w. P w z \<longleftrightarrow> \<not> O w x" by (meson AS R)
qed

lemma (in GEM) T53: "x \<noteq> u \<longrightarrow> D x (\<^bold>\<not> x)" by (meson CCP P.D_def R T10 T52)

lemma (in GEM) T54: "x \<noteq> u \<longrightarrow> (x \<^bold>+ (\<^bold>\<not> x)) =  u"
proof
  assume "x \<noteq> u"
  hence "\<exists> w. \<not> O w x" using T15 T51 by blast
  hence "\<forall> w. w \<^bold>\<le> (\<^bold>\<not> x) \<longleftrightarrow> \<not> O w x" using CCP by simp
  have "\<forall> w. O w (x \<^bold>+ (\<^bold>\<not> x)) \<longleftrightarrow> (O w x \<or> O w (\<^bold>\<not> x))" using USCP.
  thus "(x \<^bold>+ (\<^bold>\<not> x)) = u" by (meson R T13 T51 \<open>\<forall>w. (w \<^bold>\<le> \<^bold>\<not> x) = (\<not> O w x)\<close>)
qed

lemma (in GEM) T55: "y \<noteq> u \<longrightarrow> x \<^bold>\<le> (\<^bold>\<not> y) \<longleftrightarrow> D x y" using CCP P.D_def T18 T53 by blast

lemma (in GEM) T56: "x \<noteq> u \<longrightarrow> x = (\<^bold>\<not>(\<^bold>\<not>x))" by (metis R T21 T32 T47 T53 T54 T55 U)


lemma (in CEM) T57a: "O x y \<and> O w (x \<^bold>\<times> y) \<longrightarrow> O w x" using T15 T25 by blast

lemma (in GEM) T57b: "O x y \<and> O w (x \<^bold>\<times> y) \<longrightarrow> O w x"
  using CEM.T57a CEM.intro CM_axioms EM_axioms by blast

lemma (in GEM) T57c: "y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y \<longrightarrow> O x (\<^bold>\<not> y)" by (metis P.D_def T41 T51a T54)

lemma (in GEM) T57d: "O w x \<and> O x y \<and> O x (\<^bold>\<not> y) \<longrightarrow> \<not> O w (x \<^bold>\<times> y) \<longrightarrow> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
proof
  assume "O w x \<and> O x y \<and> O x (\<^bold>\<not> y)"
  show "\<not> O w (x \<^bold>\<times> y) \<longrightarrow> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
  proof
    assume "\<not> O w (x \<^bold>\<times> y)"
    have "(\<forall> w. w \<^bold>\<le> (\<^bold>\<not> y) \<longleftrightarrow> \<not> O w y)" using CCP by (metis PCP T15 \<open>O w x \<and> O x y \<and> O x (\<^bold>\<not> y)\<close> \<open>\<not> O w (x \<^bold>\<times> y)\<close>)
    have "(\<forall> w. w \<^bold>\<le> (x \<^bold>\<times> y) \<longleftrightarrow> (w \<^bold>\<le> x \<and> w \<^bold>\<le> y))" using PCP by (simp add: \<open>O w x \<and> O x y \<and> O x (\<^bold>\<not> y)\<close>)
    thus "O w (x \<^bold>\<times> (\<^bold>\<not> y))" by (smt GEM.PCP GEM_axioms P.O_def T \<open>O w x \<and> O x y \<and> O x (\<^bold>\<not> y)\<close> \<open>\<forall>w. (w \<^bold>\<le> \<^bold>\<not> y) = (\<not> O w y)\<close> \<open>\<not> O w (x \<^bold>\<times> y)\<close>)
  qed
qed

lemma (in GEM) T57e: "y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y \<longrightarrow>
(\<forall> w. O w x \<longleftrightarrow> O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y)))"
proof
  assume "y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y"
  hence "O x y" by simp
  show "\<forall> w. O w x \<longleftrightarrow> O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
    proof
      fix w
      show "O w x \<longleftrightarrow> O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
      proof
        assume "O w x"
        have "\<not> O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> y)"..
        thus "O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
        proof (rule disjE)
          assume "\<not> O w (x \<^bold>\<times> y)"
          hence "O w (x \<^bold>\<times> (\<^bold>\<not> y))" using T57d T57c \<open>O w x\<close> \<open>y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y\<close> by blast
          thus "O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"..
        next
          assume "O w (x \<^bold>\<times> y)"
          thus "O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"..
        qed
      next
        assume "O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))"
        thus "O w x"
        proof (rule disjE)
          assume "O w (x \<^bold>\<times> y)"
          hence "O x y \<and> O w (x \<^bold>\<times> y)" using \<open>O x y\<close> by blast
          thus "O w x" using T57b by blast
        next
          assume "O w (x \<^bold>\<times> (\<^bold>\<not> y))"
          have "O x (\<^bold>\<not> y)" using T57c \<open>y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y\<close> by simp
          hence "O x (\<^bold>\<not> y) \<and> O w (x \<^bold>\<times> (\<^bold>\<not> y))" using \<open>O w (x \<^bold>\<times> \<^bold>\<not> y)\<close> by blast
          thus "O w x" using T57b by blast
        qed
      qed
    qed
  qed

lemma (in GEM) T57:
"y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y \<longrightarrow> x = ((x \<^bold>\<times> y) \<^bold>+ (x \<^bold>\<times> (\<^bold>\<not> y)))"
proof
  assume "y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y"
  have "\<forall> w. O w ((x \<^bold>\<times> y) \<^bold>+ (x \<^bold>\<times> (\<^bold>\<not> y))) \<longleftrightarrow> O w (x \<^bold>\<times> y) \<or> O w (x \<^bold>\<times> (\<^bold>\<not> y))" using USCP.
  hence "\<forall> w. O w ((x \<^bold>\<times> y) \<^bold>+ (x \<^bold>\<times> (\<^bold>\<not> y))) \<longleftrightarrow> O w x"
    by (meson T57b T57c T57d \<open>y \<noteq> u \<and> O x y \<and> \<not> x \<^bold>\<le> y\<close>)
  thus "x = ((x \<^bold>\<times> y) \<^bold>+ (x \<^bold>\<times> (\<^bold>\<not> y)))" by (simp add: AS T15)
qed

subsection {* General Product *}

lemma (in GEM) T58: "x = (\<pi> z. z = x)"
proof -
  have "(\<pi> z. z = x) = (\<sigma> z. \<forall> y. x = y \<longrightarrow> z \<^bold>\<le> y)" by (simp add: \<pi>_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x = j \<longrightarrow> v \<^bold>\<le> j)  \<and> O v y))" using \<sigma>_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall>j. x = j \<longrightarrow> v \<^bold>\<le> j) \<and> O v y)" using R T10 T12 by blast
    thus "\<And>z. \<forall>y. O y z = (\<exists>v. (\<forall>j. x = j \<longrightarrow> v \<^bold>\<le> j) \<and> O v y) \<Longrightarrow> z = x" by (metis AS T11 T13)
  qed
  finally show "x = (\<pi> z. z = x)" by simp
qed

lemma (in GEM) T59: "x = (\<pi> z. x \<^bold>\<le> z)"
proof -
  have "(\<pi> z. x \<^bold>\<le> z) = (\<sigma> z. \<forall> y. x \<^bold>\<le> y \<longrightarrow> z \<^bold>\<le> y)" by (simp add: \<pi>_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x \<^bold>\<le> j \<longrightarrow> v \<^bold>\<le> j)  \<and> O v y))" using \<sigma>_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall>j. x \<^bold>\<le> j \<longrightarrow> v \<^bold>\<le> j) \<and> O v y)" using R T10 T12 by blast
    thus "\<And>z. \<forall>y. O y z = (\<exists>v. (\<forall>j. x \<^bold>\<le> j \<longrightarrow> v \<^bold>\<le> j) \<and> O v y) \<Longrightarrow> z = x" by (metis AS T11 T13)
  qed
  finally show "x = (\<pi> z. x \<^bold>\<le> z)" by simp
qed


(*
definition \<sigma>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<sigma>")
  where "\<sigma> F \<equiv> THE x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y)"
abbreviation \<sigma>x:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" [8] 9)
  where "\<sigma> x. F x \<equiv> \<sigma> F" --  "general sum or fusion of the Fs"
definition \<pi>:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<pi>")
  where "\<pi> F \<equiv> \<sigma> x. \<forall> y. F y \<longrightarrow> x \<^bold>\<le> y" -- "general products @{cite casati_parts_1999}, p. 46"
abbreviation \<pi>x:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<pi>" [8] 9)
  where "\<pi> x. F x \<equiv> \<pi> F"  --  "general sum or product of the Fs"
*)

lemma (in GEM) T60: "(\<exists> y. x \<^bold>< y) \<longrightarrow> x = (\<pi> z. x \<^bold>< z)" nitpick [user_axioms] oops

lemma (in GEM) T61:
"(\<exists> x. \<forall> y. F y \<longrightarrow> x \<^bold>\<le> y) \<longrightarrow> (\<pi> x. F x) = (THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<^bold>\<le> x))" nitpick [user_axioms] oops

(*

lemma (in GEM) T61a: "(\<sigma> x. \<forall> y. F y \<longrightarrow> x \<^bold>\<le> y) = (THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<^bold>\<le> x))" nitpick oops

It seems as if Simons thought "(THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<^bold>\<le> x))" is an alternative way
of defining general product, but the definitions are not equivalent. Really?!

*)

subsection {* General Sum *}

lemma (in EM) T62: "x = (\<sigma> z. z = x)" by (metis (full_types) T10 UGS) 
lemma (in EM) T63: "x = (\<sigma> z. z \<^bold>\<le> x)" by (metis (no_types, lifting) UGS T10 T15)
lemma (in M) T64: "\<exists> y. y \<^bold>< x \<longrightarrow> x = (\<sigma> z. z \<^bold>< x)" using T1 by auto

lemma (in GEM) T65:
"(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> x. F x) = z" using UGS by simp
  have "(THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y)) = z"
  proof (rule the_equality)
    show "\<forall>y. z \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y)"
    proof
      fix y
      show "z \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y)"
      proof
        assume "z \<^bold>\<le> y" 
        thus "(\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y)" using T10 T15 z by blast
        next
          assume "(\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y)"
          thus "z \<^bold>\<le> y" using T10 T15 \<open>\<forall>z. F z \<longrightarrow> z \<^bold>\<le> y\<close> z by blast
        qed
      qed
      show "\<And>x. \<forall>y. (x \<^bold>\<le> y) = (\<forall>z. F z \<longrightarrow> z \<^bold>\<le> y) \<Longrightarrow> x = z"
        using AS R \<open>\<forall>y. (z \<^bold>\<le> y) = (\<forall>z. F z \<longrightarrow> z \<^bold>\<le> y)\<close> by blast
    qed
    thus "(\<sigma> x. F x) = (THE x. \<forall> y. x \<^bold>\<le> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<^bold>\<le> y))" 
      using  \<open>(\<sigma> x. F x) = z\<close> by metis
  qed

lemma (in GEM) T66:
"(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<^bold>\<le> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "z = (\<sigma> x. F x)" using UGS by simp
  have "(THE x. (\<forall> y. F y \<longrightarrow> y \<^bold>\<le> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z))) = z"
  proof (rule the_equality)
    show "(\<forall>y. F y \<longrightarrow> y \<^bold>\<le> z) \<and> (\<forall>y. O y z = (\<exists>z. F z \<and> O y z))" using T10 T15 z by blast
    show " \<And>x. (\<forall>y. F y \<longrightarrow> y \<^bold>\<le> x) \<and> (\<forall>y. O y x = (\<exists>z. F z \<and> O y z)) \<Longrightarrow> x = z"
      by (meson AS P.D_def SS T11 \<open>(\<forall>y. F y \<longrightarrow> y \<^bold>\<le> z) \<and> (\<forall>y. O y z = (\<exists>z. F z \<and> O y z))\<close>)
  qed
  thus "(\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<^bold>\<le> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))" 
    using  \<open>z = (\<sigma> x. F x)\<close> by metis
qed

lemma (in GEM) T67: "O x (\<sigma> y. F y) \<longrightarrow> (\<exists> z. F z \<and> O z x)" nitpick oops

lemma (in GEM) T67weak: "(\<exists> y. F y) \<longrightarrow> O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)"
proof
  assume "(\<exists> y. F y)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z" using UGS by simp
  thus "O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)" by (metis z)
qed

lemma (in GEM) T68: "D x (\<sigma> y. F y) \<longrightarrow> (\<forall> z. F z \<longrightarrow> D z x)" by (metis P.D_def PS R T18 T19 T21)

lemma (in GEM) T69a: "(\<exists> x. D a x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. D a x \<and> O x y))" using F.

lemma (in GEM) T69: "a \<noteq> u \<longrightarrow> (\<^bold>\<not> a) = (\<sigma> z. D a z)"
proof
  assume "a \<noteq> u"
  hence "x \<^bold>\<le> (\<^bold>\<not> a) \<longleftrightarrow> D a x" using T55 T18 by blast
  have "\<exists> x. D a x" using T21 T51 \<open>a \<noteq> u\<close> T53 by blast
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. D a x \<and> O x y)" using T69a by blast
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. D a x \<and> O x y)"..
  hence "(\<sigma> x. D a x) = z" using UGS by simp
  thus "(\<^bold>\<not> a) = (\<sigma> z. D a z)" by (metis AS CCP P.D_def T10 T17 T20 z)
qed

lemma (in GEM) T70: "(\<sigma> x. F x) \<^bold>\<le> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))" oops

lemma (in GEM) T70weak: "(\<exists> x. F x) \<and> (\<exists> x. G x) \<longrightarrow>
 (\<sigma> x. F x) \<^bold>\<le> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
proof
  assume "(\<exists> x. F x) \<and> (\<exists> x. G x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z" using UGS by simp
  have "(\<exists> x. G x)" by (simp add: \<open>(\<exists>x. F x) \<and> (\<exists>x. G x)\<close>)
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)" using F by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)"..
  hence "(\<sigma> y. G y) = z" using UGS by simp
  show "(\<sigma> x. F x) \<^bold>\<le> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
  proof
    assume "(\<sigma> x. F x) \<^bold>\<le> (\<sigma> y. G y)"
    thus "(\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))" by (metis D_def T10 T15 T17 T68 \<open>(\<sigma> y. G y) = z\<close> z)
  qed
qed

(*
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
*)

end

