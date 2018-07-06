theory Mereotopology7
imports Mereology17
begin
section {* theories *}

subsection {* ground Topology *}

text{* ground Topology (T)- "It introduces Connectedness as primitive relation between Individuals
and it's parts. Since, Connections seem to be sharing relations, It is assumed to be
reflexive and symmetric both but not transitive" @{cite "casati_parts_1999"} *}

locale T =
 fixes C :: "i \<Rightarrow> i \<Rightarrow> bool" ("C")--"Connectedness"
 assumes reflexivity: "C x x" -- "reflexivity of connectedness "
 and symmetry: "C x y \<longrightarrow> C y x" -- "symmetry of connectedness"

begin

definition E :: "i \<Rightarrow> i \<Rightarrow> bool" ("E")--"Enclosed- since relations are shared with parts, It is assumed 
to be enclosed in it"
  where "E x y \<equiv> \<forall>z. C z x \<longrightarrow> C z y"
end

lemma (in T) enclosure_reflexivity: "E x x" 
  by (simp add: E_def)
lemma (in T) enclosure_transitivity: "E x y \<longrightarrow> E y z \<longrightarrow> E x z " 
  by (simp add: E_def)

(* Hi Manikaran. The next lemma is the first thing that's a bit puzzling so I'm adding some text
here *) 

text {* According to Casati and Varzi ``if C is extensional then E is also antisymmetric. What do
they mean by `` @{term "C"} is extensional'' here? I think they must mean that if two things are
connected to all of the same things, then they are the same things, viz: *}

lemma (in T) connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y" nitpick oops 

  text {* That is not a theorem in T, and it's not clear to me whether it should be a theorem or not.
So it will be interesting to see whether it is true in any of the stronger theories later. In any
case, if that's what extensionality means in this context, we can now check  *}

lemma (in T) assumes connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y"
shows enclousre_antisymmetry: "E x y \<and> E y x \<longrightarrow> x = y"
  using E_def connection_extensional symmetry by blast

text {* This seems right, so that's some evidence that this is what they mean by antisymmetry.
But since we are only guessing here, we should keep our eyes open as we look at the literature
for a more explicit definition of extensionality to check whether we are on the right track. *}

section{* Ground Mereotopology *}


text{* Ground mereotopology (MT) It involves the connection between Mereology and Topology *}

locale MT = M + T +
  assumes MTC : "P x y \<longrightarrow> E x y" --" Monotonicity "

begin

text {* The following lemma could be used as an alternative axiom @{cite "casati_parts_1999"} p. 54:  *}

lemma "P x y \<longrightarrow> (\<forall>z. C x z \<longrightarrow> C z y)"
  using E_def MTC symmetry by blast

text {* Note that connection is still not extensional in MT: *}

lemma connection_extensional: "(\<forall> z. C x z \<longleftrightarrow> C y z) \<longleftrightarrow> x = y" nitpick oops

text{* MTC immediately implies that mereological overlap is a form of connection
@{cite "casati_parts_1999"} p. 54: *}

lemma overlap_imnplies_connection: "O x y \<longrightarrow> C x y"
  using E_def MTC O_def T.symmetry T_axioms reflexivity by blast

text {* But the converse may fail @{cite "casati_parts_1999"} p. 54: *}

lemma  "C x y \<longrightarrow> O x y" nitpick oops

text {* This leads us to define external connection, where x is externally connected to y if and
only if x and y are connected but do not have a common part @{cite "casati_parts_1999"}: *}

definition EC :: "i \<Rightarrow> i \<Rightarrow> bool" ("EC")--"External connection"
  where "EC x y \<equiv> C x y \<and> \<not> O x y"

text {* External connection is irreflexive and symmetric:  *}

lemma external_connection_irreflexive: "\<not> EC x x"
  by (simp add: EC_def T9)
lemma external_connection_symmetric: "EC x y \<longrightarrow> EC y x"
  using EC_def T10 symmetry by blast

text {* but not transitive: *}

lemma external_connection_transitive: "EC x y \<longrightarrow> EC y z \<longrightarrow> EC x z" nitpick [user_axioms] oops

text{* The following further relations are also defined in terms of connectedness, parthood and overlap: *}

definition IP :: "i \<Rightarrow> i \<Rightarrow> bool" ("IP") -- "Internal part - part of y connected only to overlappers of y"
  where
"IP x y \<equiv> P x y \<and> (\<forall>z. C z x \<longrightarrow> O z y)"

text {* For example, Ethiopia is an internal part of Africa because every country connected to
Ethiopia overlaps Africa. But Egypt is not an internal part of Africa, because Egypt is connected
to Israel, and Israel does not overlap Africa. *}

text {* Internal parthood is neither reflexive nor irreflexive, but it is antisymmetric and
transitive: *}

lemma internal_part_reflexive: "IP x x" nitpick [user_axioms] oops
lemma internal_part_irreflexive: "\<not> IP x x" nitpick [user_axioms] oops
lemma internal_part_antisymmetry: "IP x y \<longrightarrow> IP y x \<longrightarrow> x = y" using AS IP_def by blast
lemma internal_part_transitivity: "IP x y \<longrightarrow> IP y z \<longrightarrow> IP x z" using IP_def T overlap_imnplies_connection by blast

definition TP :: "i\<Rightarrow>i\<Rightarrow>bool" ("TP") -- "Tangential part"
  where
"TP x y \<equiv> P x y \<and> \<not> IP x y"

text {* As long as something has a tangential part, it is a tangential part of itself: *}

lemma tangential_part_reflexivity: "\<exists> y. TP y x \<longrightarrow> TP x x" by simp

text {* Likewise, tangential parthood is antisymmetric, but not transitive: *}

lemma tangential_part_antisymmetry: "TP x y \<longrightarrow> TP y x \<longrightarrow> x = y" using AS TP_def by blast
lemma tangential_part_transitivity: "TP x y \<longrightarrow> TP y z \<longrightarrow> TP x z" nitpick [user_axioms] oops

definition IO :: "i\<Rightarrow>i\<Rightarrow>bool" ("IO")--"Internal overlap"
  where
"IO x y \<equiv> \<exists> z. IP z x \<and> IP z y"

lemma IO_reflexive: "\<exists> y. IO y x \<longrightarrow> IO x x" by simp
lemma IO_symmetric: "IO x y \<longrightarrow> IO y x" using IO_def by blast
lemma IO_transitive: "IO x y \<longrightarrow> IO y z \<longrightarrow> IO x z" nitpick [user_axioms] oops

definition TO :: "i\<Rightarrow>i\<Rightarrow>bool" ("TO")--"Tangential overlap"
  where
"TO x y \<equiv> O x y \<and> \<not>IO x y"

lemma TO_reflexive: "\<exists> y. TO y x \<longrightarrow> TO x x" by simp
lemma TO_symmetric: "TO x y \<longrightarrow> TO y x" using IO_symmetric T10 TO_def by blast
lemma IO_transitive: "IO x y \<longrightarrow> IO y z \<longrightarrow> IO x z" nitpick [user_axioms] oops

definition IU :: "i\<Rightarrow>i\<Rightarrow> bool" ("IU")--"Internal underlap"
  where
"IU x y \<equiv> \<exists>z. IP x z \<and> IP y z"

definition TU :: "i\<Rightarrow>i\<Rightarrow>bool" ("TU")--"Tangentially underlap"
  where
"TU x y \<equiv> U x y \<and> \<not> IU x y"

text{* More generally, For each mereological predicate "\<phi>" we can define corresponding
 mereotopological predicates replacing "I\<phi>" and "T\<phi>" by substituting IP and TP (respectively)
for each occurrence of 'P' in the definies.@{cite "casati_parts_1999" } P-55,4.2.for example.. *}

definition IPP :: "i \<Rightarrow> i \<Rightarrow> bool" ("IPP")--"internal proper part"
  where
"IPP x y \<equiv> IP x y \<and> \<not>(IP y x)"

(*
definition TPP :: "i\<Rightarrow>i\<Rightarrow>bool" ("TPP")--"tangential proper part"
  where
"TPP x y \<equiv> TP x y \<and> \<not>( TP y x)"
text{* just like that all the predicates, defined in the mereology subsection, can be converted to 
mereotopological predicates *}
*)

text{* As we go through the theory of mereotopology,concept of self connectedness begins to rise; A
cat's tail is connected to the rest of it's body-there is nothing separating them. And surely
the two don't overlap-there are no common parts. *}

text{* Below we define the predicate for self connectedness that makes the difference between solid
wholes (such as table or a cup) and scattered wholes (such as bikini or a broken glass; to define self
connectedness we say that x is self connected if any two parts that make the whole of x are 
connected to each other: *}

definition SC :: "i \<Rightarrow> bool" ("SC") -- "Self-connectedness"
  where
"SC x \<equiv> \<forall> y.\<forall> z.(\<forall> w. O w x \<longleftrightarrow> O w y \<or> O w z) \<longrightarrow> C y z"

text {* This definition basically says that x is self-connected if, if x is a fusion of y and z,
then y and z are connected. *}

end 

section {* Closed Mereotopology *}

locale CMT = CM + MT +
  assumes connection_implies_underlap: "C x y \<longrightarrow> U x y "

text {* Casati and Varzi say we get the following theorem @{cite "casati_parts_1999"} p. 58. And
we should. If x and y are connected, then according to the axiom they underlap. So then according to
sum closure they have a sum. And since x and y are connected, and self-connected, it seems as if this
sum should be self-connected too: *}

lemma (in CMT) SCC: "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists>z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y))" nitpick [user_axioms] oops

text {* However, nitpick says otherwise. I suspect this is a mistake in Casati and Varzi. Alternatively,
it may be a mistake in our own work. In either case, let's just press on, bearing this in mind, until
we discover which one. *}
  
text {* One possibility is that closed mereotopology is too weak. So let's try closed minimal
mereotopology. *}

locale CMMT = CMM + CMT

text {* Now nitpick doesn't work anymore, so perhaps the problem is fixed. If so, we know we will have
to use weak supplementation (the main axiom of minimal mereology), as well as the closure axioms: *}

lemma (in CMMT) "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists>z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y))"
proof
  assume "C x y \<and> SC x \<and> SC y"
  have "C x y" by (simp add: \<open>C x y \<and> SC x \<and> SC y\<close>)
  with connection_implies_underlap have "U x y"..
  with SC have "\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w x \<or> O w y)"..
  then obtain c where c: "\<forall> w. O w c \<longleftrightarrow> (O w x \<or> O w y)"..
  have "\<forall> y.\<forall> z.(\<forall> w. O w c \<longleftrightarrow> O w y \<or> O w z) \<longrightarrow> C y z"
  proof
    fix a
    show "\<forall> z.(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w z) \<longrightarrow> C a z"
    proof
      fix b
      show "(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w b) \<longrightarrow> C a b"
      proof
        assume "(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w b)"
        show "C a b"
        proof cases
          assume "O a b"
          thus "C a b" by (simp add: overlap_imnplies_connection)
        next
          assume "\<not> O a b"
          thus "C a b" sorry
        qed
      qed
    qed
  qed
  hence "SC c" using SC_def by blast
  hence "SC c \<and> (\<forall> w. O w c \<longleftrightarrow> O w x \<or> O w y)" by (simp add: c)
  thus "\<exists> z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y)"..
qed



text {* First though, let's try helping ourselves to closed extensional mereotopology - maybe things
will be easier with the even stronger theory? *}

locale CEMT = CEM + CMT

lemma (in CEMT) "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists> z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y))"
proof
  assume "C x y \<and> SC x \<and> SC y"
  hence "C x y"..
  with connection_implies_underlap have "U x y"..
  with SC have "\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w x \<or> O w y)"..
  then obtain c where c: "\<forall> w. O w c \<longleftrightarrow> (O w x \<or> O w y)"..
  have "\<forall> y.\<forall> z.(\<forall> w. O w c \<longleftrightarrow> O w y \<or> O w z) \<longrightarrow> C y z"
  proof
    fix a
    show "\<forall> z.(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w z) \<longrightarrow> C a z"
    proof
      fix b
      show "(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w b) \<longrightarrow> C a b"
      proof
        assume "(\<forall> w. O w c \<longleftrightarrow> O w a \<or> O w b)"
        thus "C a b" sorry
      qed
    qed
  qed
  hence "SC c" using SC_def by blast
  hence "SC c \<and> (\<forall> w. O w c \<longleftrightarrow> O w x \<or> O w y)" by (simp add: c)
  thus "\<exists> z. SC z \<and> (\<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y)"..
qed

text {* I'm out of ideas at the same point. I need to think about this longer. *}

text {* In CEMT, there's another version of the same theorem. Maybe if we try to prove that instead
it will give us a clue: *}


lemma (in CEMT) "(C x y \<and> SC x \<and> SC y) \<longrightarrow> SC (x \<^bold>+ y)" 
proof
  assume "C x y \<and> SC x \<and> SC y"
  hence "C x y"..
  with connection_implies_underlap have "U x y"..
  thus "SC (x \<^bold>+ y)"  sorry
qed

text {* After having looked at the mereology file, I've realised that most of the lemmas concerning sums
are proved in closed extensional mereology with an additional axiom stating there is a universe. I will
have to fix that soon. But now it makes more sense to try to prove this in CEMU with universe, to take advantage
of all the lemmas. Thus: *}

locale CEMUT = CEMU + CMT

lemma (in CEMUT) "(C x y \<and> SC x \<and> SC y) \<longrightarrow> SC (x \<^bold>+ y)"
proof
  assume "C x y \<and> SC x \<and> SC y"
  hence "SC x \<and> SC y"..
  hence "SC x"..
  hence "\<forall> y. \<forall> z. (\<forall> w. O w x \<longleftrightarrow> O w y \<or> O w z) \<longrightarrow> C y z" using SC_def by simp
  have "SC y" by (simp add: \<open>SC x \<and> SC y\<close>)
  hence "\<forall> v. \<forall> z. (\<forall> w. O w y \<longleftrightarrow> O w v \<or> O w z) \<longrightarrow> C v z" using SC_def by simp
  have "\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> (O w x \<or> O w y)" using USCP.
  hence "\<forall> v.\<forall> z.(\<forall> w. O w (x \<^bold>+ y) \<longleftrightarrow> O w v \<or> O w z) \<longrightarrow> C v z"  sorry
  thus "SC (x \<^bold>+ y)" using SC_def by blast
qed




text {* I was hoping that with all the lemmas in the mereology document, Isabelle would be able to prove
this one automatically - but no such luck.

What should we do now? A few months ago (which I asked that question on stack exchange, I was stuck on
a similar problem with mereology.

Eventually, it turned out there was a mistake in Casati and Varzi's book, which had been addressed
(with proofs!) in the literature.

So I think the best thing for us to do now is to look further afield to see if why can find proofs,
or disproofs, of these conjectures in the literature.

 *}

 (* 
  fix p q r s
  assume "C x y \<and> SC x \<and> SC y"
  hence "\<forall> w.(O w x \<longleftrightarrow> O w p \<or> O w q) \<longrightarrow> C p q"
    using SC_def by blast
  hence "\<forall>w.(O w y \<longleftrightarrow> O w r \<or> O w s) \<longrightarrow> C r s"
    using SC_def \<open>C x y \<and> SC x \<and> SC y\<close> by auto
    hence "\<forall>w.(\<exists>p.\<exists>q.\<exists>r.\<exists>s.(O w p \<or> O w q)\<and>(O w r \<or> O w s))"
      using T9 by auto
    hence "\<forall>w.(\<exists>p.\<exists>q.\<exists>r.\<exists>s.( C p q \<and> C r s))"
      using \<open>C x y \<and> SC x \<and> SC y\<close> by blast
  hence    "((\<forall>w.(O w x \<longleftrightarrow> O w p \<or> O w q)\<longrightarrow>C p q)) \<and>  ((\<forall>w.(O w y \<longleftrightarrow> O w r \<or> O w s)\<longrightarrow>C r s))"
    using \<open>\<forall>w. O w x = (O w p \<or> O w q) \<longrightarrow> C p q\<close> \<open>\<forall>w. O w y = (O w r \<or> O w s) \<longrightarrow> C r s\<close> by blast
  hence "\<exists>z.\<forall>w.(C z p \<or> C z q)\<and>(C z r \<or> C z s)"
    by (metis O_def SC_def \<open>C x y \<and> SC x \<and> SC y\<close>)
  hence "\<exists>z.(SC z)"
    using \<open>C x y \<and> SC x \<and> SC y\<close> by auto
  hence "\<exists>z.(SC z \<and> C z x \<and> C z y)" 
      using R \<open>C x y \<and> SC x \<and> SC y\<close> by blast
    hence "\<exists>z.\<exists>p.\<exists>r.\<exists>q.\<exists>s.(P p x \<and> P q x \<and> P r y \<and> P s y)\<and>((C z p \<or> C z q)\<and>(C z r \<or> C z s))\<and> SC z\<longrightarrow>(((\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))))"
   using AS by blast
  hence "\<exists>p.\<exists>r.\<exists>q.\<exists>s.\<exists>z.(P p x \<and> P q x \<and> P r y \<and> P s y)\<and>((C z p \<or> C z q)\<and>(C z r \<or> C z s))\<and> SC z"
    by (smt R T3 \<open>C x y \<and> SC x \<and> SC y\<close>)
  hence "\<exists>z.(\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))"
    using CMT.axioms(3) CMT_axioms CMT_axioms_def SC \<open>C x y \<and> SC x \<and> SC y\<close> by auto
  hence " (\<exists>z.(SC z \<and> (\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))))"
    by (metis (mono_tags, hide_lams) SC_def \<open>C x y \<and> SC x \<and> SC y\<close>)
  hence  "(C x y \<and> SC x \<and> SC y) \<longrightarrow> (\<exists>z.(SC z \<and> (\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))))"
    by blast
  have "(C x y \<and> SC x \<and> SC y)"
    by (simp add: \<open>C x y \<and> SC x \<and> SC y\<close>)
  hence "(\<exists>z.(SC z \<and> (\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))))"
    using \<open>\<exists>z. SC z \<and> (\<forall>w. O w z = (O w x \<or> O w y))\<close> by blast
  thus "(\<exists>z.(SC z \<and> (\<forall>w.(O w z \<longleftrightarrow> O w x \<or> O w y))))" 
    by blast
qed
*)

section {* Classical Extensional Mereotopology *}

locale GEMT = GEM + MT

begin
lemma (in GEMT) "C x y \<longrightarrow> U x y" 
  using EU by blast

lemma "\<forall> x. IP x u"
  by (simp add: IP_def T11 T51a)

definition i :: "(i\<Rightarrow>i)" ("\<^bold>i")--"interior"
  where
"\<^bold>i x \<equiv> \<sigma> z. IP z x"

lemma UGSl: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)) \<longrightarrow> (\<sigma> z. IP z x) = a" using UGS.

lemma i_intro: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)) \<longrightarrow> (\<^bold>i x) = a" using UGSl i_def by simp

lemma interior_fusion: "(\<exists> y. IP y x) \<longrightarrow> (\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y))" using F.

lemma Pixx: "(\<exists> y. IP y x) \<longrightarrow> P (\<^bold>i x) x" -- "the interior of an individual is part of it"
proof
  assume "(\<exists> y. IP y x)"
  with interior_fusion have "\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  then obtain a where a: "\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z x \<and> O z y)"..
  with i_intro have "(\<^bold>i x) = a"..
  thus "P (\<^bold>i x) x"
    by (metis IP_def T10 T12 T13 a)
qed

lemma Oixx: "(\<exists> y. IP y x) \<longrightarrow> O (\<^bold>i x) x"
  by (simp add: Pixx T11)
lemma Cixx:  "(\<exists> y. IP y x) \<longrightarrow> C (\<^bold>i x) x" -- "individuals are connected to their interiors"
  by (simp add: Pixx T11 overlap_imnplies_connection)
lemma Eixx:  "(\<exists> y. IP y x) \<longrightarrow> E (\<^bold>i x) x" -- "individuals enclose their interiors"
  by (simp add: MTC Pixx)

lemma "(\<exists> y. IP y x) \<longrightarrow> (\<exists> y. IP z x) \<longrightarrow> P z x \<longrightarrow> P (\<^bold>i z) (\<^bold>i x)" nitpick  oops

definition e :: "(i\<Rightarrow>i)" ("\<^bold>e")--"exterior"
  where
"\<^bold>e x \<equiv> \<^bold>i (\<^bold>\<not> x)"

lemma UGSl2: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<^bold>\<not> x) \<and> O z y)) \<longrightarrow> (\<^bold>i (\<^bold>\<not> x)) = a" using UGSl i_def by simp

lemma e_intro: "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<^bold>\<not> x) \<and> O z y)) \<longrightarrow> (\<^bold>e x) = a" using UGSl2 e_def by simp

(*
lemma e_intro:  "(\<forall> y. O y a \<longleftrightarrow> (\<exists> z. \<forall> w. (P w z \<longleftrightarrow> \<not> O w x) \<and> IP y z)) \<longrightarrow> (\<^bold>e x) = a"
  using asdfdasfdsa C_def by (meson IP_def T10 T11 U)
*)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> (\<exists> a. \<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<^bold>\<not> x) \<and> O z y))"
  by (simp add: GEMT.interior_fusion GEMT_axioms)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> \<not> P (\<^bold>e x) x" by (metis Pixx T19 T21 T53 e_def)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> \<not> P x (\<^bold>e x)" by (metis GEMT.Pixx GEMT_axioms T21 T53 e_def)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> \<not> O x (\<^bold>e x)"  by (metis D_def Pixx T10 T55 e_def)

definition c :: "i\<Rightarrow>i" ("\<^bold>c")--"closure"
  where
"\<^bold>c x \<equiv> \<^bold>\<not> (\<^bold>e x)"

lemma c_intro:  "(\<forall> y. P y a \<longleftrightarrow> \<not> O y (\<^bold>e x)) \<longrightarrow> (\<^bold>c x) = a" using c_def using AS CCP R by blast

lemma closure_closure: "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> (\<exists> a. \<forall> y. P y a \<longleftrightarrow> \<not> O y (\<^bold>e x))"
proof
  assume antecedent: "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x))"
  hence "\<exists> y. IP y (\<^bold>\<not> x)"..
  with interior_fusion have "(\<exists> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. IP z (\<^bold>\<not> x) \<and> O z y))"..
  then obtain a where a: "\<forall> y. O y a \<longleftrightarrow> (\<exists> z. IP z (\<^bold>\<not> x) \<and> O z y)"..
  with e_intro have "(\<^bold>e x) = a"..
  from antecedent have "x \<noteq> u"..
  hence "\<forall> y. P y (\<^bold>\<not> x) \<longleftrightarrow> D y x" by (simp add: T55)
  thus "(\<exists> a. \<forall> y. P y a \<longleftrightarrow> \<not> O y (\<^bold>e x))" by (metis CC D_def IP_def \<open>\<^bold>e x = a\<close> a)
qed

lemma closure_inclusion: "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> P x (\<^bold>c x)"
  by (metis Pixx T20 T51a T53 T55 c_def e_def)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> O x (\<^bold>c x)"
  by (metis CCP Pixx T21 T51a T53 T56 c_def e_def)

lemma "x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> x)) \<longrightarrow> C x (\<^bold>c x)"
  by (metis CCP Pixx T11 T21 T34 T53 T54 T57c c_def e_def overlap_imnplies_connection)

definition b :: "i\<Rightarrow>i" ("\<^bold>b")--"boundary"
  where
"\<^bold>b x \<equiv> \<^bold>\<not> (\<^bold>i x \<^bold>+ \<^bold>e x)"


end
text{* Note that all the integrated operators in GEMT(GEM+MT) are distinguished by bold font *}

text{* These integrated operators are partially defined, unless we assume the existence of a null 
individual that is part of everything *}

text{* Even so,in GEMT these operators are rather well-behaved. *}

text{* In particular, we can get closer to standard topological theories by supplementing the axiom
of symmetry and reflexivity and the monotonicity axiom of connectedness, with the mereologized 
analogues of the standard kuratowski (1922) axioms for topological closure@{cite "casati_parts_1999"}
, P.59 .*}

locale GEMTC = GEMT + 
  assumes closure_idempotence: "\<^bold>c x \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> (\<^bold>c x))) \<longrightarrow> \<^bold>c (\<^bold>c x) = \<^bold>c x"
  assumes closure_distributes_over_sum:
    "(x \<^bold>+ y) \<noteq> u \<and> (\<exists> y. IP y (\<^bold>\<not> (x \<^bold>+ y))) \<longrightarrow> \<^bold>c (x \<^bold>+ y) = \<^bold>c x \<^bold>+ \<^bold>c y"


begin


text {* Equivalently, we could use the axioms for the interior operator @{cite "casati_parts_1999"}
p.59: *}

lemma interior_inclusion : "\<exists> y. IP y x \<longrightarrow> P (\<^bold>i x) x" by (simp add: IP_def)
lemma interior_idempotence : "\<exists> y. IP y x \<longrightarrow> \<^bold>i (\<^bold>i x) = \<^bold>i x"
  by (metis IP_def T11 T9 i_intro)

lemma p_intro : "(\<forall>z. P a z \<longleftrightarrow> (P z (\<^bold>i x) \<and> P z (\<^bold>i y))) \<longrightarrow> ((\<^bold>i x) \<^bold>\<times> (\<^bold>i y)) = a "
  by (metis (mono_tags, hide_lams) AS T11 T52 U)  

lemma p : "(\<forall>z. P a z \<longleftrightarrow> (P z x \<and> P z y)) \<longrightarrow> (x \<^bold>\<times> y) = a "
  by (metis AS O_def PCP T11 T13)

lemma pi : "(\<exists>w. IP a w \<and> (\<forall>v. P w v \<longleftrightarrow> P v x \<and> P v y)\<longrightarrow> a = \<^bold>i (x \<^bold>\<times> y))"
  by (meson T7)
lemma pi2 : "(\<forall>z. O z a \<longleftrightarrow> (\<exists>w. IP w (x \<^bold>\<times> y) \<and> O w z))\<longrightarrow> \<^bold>i (x \<^bold>\<times> y) = a"
  by (simp add: GEMT.UGSl GEMT_axioms i_def)
lemma Px : "\<exists>w. IP (x \<^bold>\<times> y) w \<longrightarrow> (\<forall>v. P w v \<longleftrightarrow> P v x \<and> P v y)"
  by (meson IP_def O_def T13)
lemma "(\<forall>v.\<exists>w. P w v \<and> P v x \<and> P v y\<longrightarrow> P w x \<and> P w y)"
  by auto
lemma Pi3 : "\<exists>w. IP (x \<^bold>\<times> y) w \<longrightarrow> P w x \<and> P w y"
  using IP_def by blast

lemma pp : "(\<exists>z. IP z (x \<^bold>\<times> y)) \<longrightarrow>P (\<^bold>i (x \<^bold>\<times> y)) (x \<^bold>\<times> y)"
  using Pixx by auto

lemma interior_distributes_over_product : "(\<exists> z. IP z (x \<^bold>\<times> y) ) \<longrightarrow> \<^bold>i (x \<^bold>\<times> y) = \<^bold>i x \<^bold>\<times> \<^bold>i y" nitpick oops 
(*proof
  assume "\<exists>z. IP z (x \<^bold>\<times> y)"
  hence "\<exists>z. P z (\<^bold>i (x \<^bold>\<times> y))"
    using R by blast
  obtain z where z: "P z (\<^bold>i (x \<^bold>\<times> y))"
    using \<open>\<exists>z. z \<^bold>\<le> \<^bold>i (x \<^bold>\<times> y)\<close> by blast
  hence "(\<exists>p. IP p x) \<and> (\<exists>z. IP z y)"sledgehammer
*)
lemma "x \<noteq> u \<longrightarrow> \<^bold>b x = \<^bold>b (\<^bold>\<not>x)"
  using T32 T56 b_def e_def by auto

lemma b_intro : "(\<forall>w. P w a \<longleftrightarrow> \<not> O w (\<^bold>i x \<^bold>+ \<^bold>e x)) \<longrightarrow> \<^bold>b x = a"
  by (metis AS CCP O_def T11 b_def)
lemma b : "x \<noteq> u \<and> (\<^bold>b x = a)\<longrightarrow> \<not> (\<exists>y. IP y a)"sorry
(* proof 
  fix a
  assume "\<^bold>b x = a"
  hence "(\<forall>y. O y a \<longleftrightarrow> (\<not> P y (\<^bold>i x) \<or> \<not> P y (\<^bold>e x)))"sledgehammer 
*)
lemma "x \<noteq> u \<longrightarrow> \<^bold>b (\<^bold>b x) = \<^bold>b x" oops
lemma "x \<noteq> u \<longrightarrow> \<^bold>b (x \<^bold>\<times> y) \<^bold>+ \<^bold>b (x \<^bold>+ y) = \<^bold>b x \<^bold>+ \<^bold>b y" oops

lemma "\<not> (\<forall> x. C x a) \<longrightarrow> (\<forall> y. P y (\<^bold>e a) \<longleftrightarrow> \<not> C y a)" oops

lemma "x \<noteq> u \<longrightarrow> (\<forall> y. P y (\<^bold>c x) \<longleftrightarrow> P y x \<or> (\<forall> z. P z y \<longrightarrow> C z x))" oops

lemma (in GEMT) SC_def2:  "SC x \<longleftrightarrow> (\<forall> y z. x = (y \<^bold>+ z) \<longrightarrow> C y z)"
proof
  assume "SC x"
  hence "\<forall> y z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z" using SC_def by simp
  thus "(\<forall> y z. x = (y \<^bold>+ z) \<longrightarrow> C y z)" using USCP by simp
next
  assume "\<forall> y z. x = (y \<^bold>+ z) \<longrightarrow> C y z"
  have "\<forall> y z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
  proof fix y
    show "\<forall> z. (\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
    proof fix z
      show "(\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> C y z"
      proof
        assume "\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)"
        with sum_intro have "x = (y \<^bold>+ z)"..
        thus "C y z" using \<open>\<forall>y z. x = y \<^bold>+ z \<longrightarrow> C y z\<close> by blast
      qed
    qed
  qed
  thus "SC x" using SC_def by simp
qed
lemma (in GEM) funny_lemma: "(O x y \<and> O x z \<longrightarrow> (P x (y \<^bold>+ z) \<longrightarrow>  x = ((x \<^bold>\<times> y) \<^bold>+ (x \<^bold>\<times> z))))"sorry



lemma (in GEM) another_funny_lemma:
"x \<^bold>+ y = w \<^bold>+ v \<longrightarrow> \<not> (O v x \<and> O w x \<or> O v y \<and> O w y) \<longrightarrow> x = w \<and> y = v \<or> x = v \<and> y = w" sorry

lemma (in GEMTC) "(C x y \<and> SC x \<and> SC y) \<longrightarrow> SC (x \<^bold>+ y)"
proof
  assume "C x y \<and> SC x \<and> SC y"
  have "\<forall> v w. (x \<^bold>+ y) = (v \<^bold>+ w) \<longrightarrow> C v w"
  proof
    fix v
    show "\<forall> w. (x \<^bold>+ y) = (v \<^bold>+ w) \<longrightarrow> C v w"
    proof
      fix w
      show "(x \<^bold>+ y) = (v \<^bold>+ w) \<longrightarrow> C v w"
      proof
        assume "(x \<^bold>+ y) = (v \<^bold>+ w)"
        show "C v w"
        proof (cases)
          assume "O v x \<and> O w x \<or> O v y \<and> O w y"
          thus "C v w"
          proof (rule disjE)
            assume "O v x \<and> O w x"
            hence "P x (v \<^bold>+ w) \<longrightarrow>  x = ((x \<^bold>\<times> v) \<^bold>+ (x \<^bold>\<times> w))" by (simp add: T10 funny_lemma)
            have "P x (v \<^bold>+ w)" by (metis T34 \<open>x \<^bold>+ y = v \<^bold>+ w\<close>)
            hence "x = ((x \<^bold>\<times> v) \<^bold>+ (x \<^bold>\<times> w))"
              using \<open>x \<^bold>\<le> v \<^bold>+ w \<longrightarrow> x = x \<^bold>\<times> v \<^bold>+ x \<^bold>\<times> w\<close> by blast
            hence "C (x \<^bold>\<times> v) (x \<^bold>\<times> w)" using SC_def2 \<open>C x y \<and> SC x \<and> SC y\<close> by blast
            hence "C v (x \<^bold>\<times> w)" by (metis E_def MTC PCP R T24 \<open>O v x \<and> O w x\<close> symmetry)
            thus "C v w" using E_def MTC PCP R T10 \<open>O v x \<and> O w x\<close> by blast
        next
          assume "O v y \<and> O w y"
          hence "P y (v \<^bold>+ w) \<longrightarrow>  y = ((y \<^bold>\<times> v) \<^bold>+ (y \<^bold>\<times> w))" by (simp add: T10 funny_lemma)
            have "P y (v \<^bold>+ w)" by (metis T35 \<open>x \<^bold>+ y = v \<^bold>+ w\<close>)
            hence "y = ((y \<^bold>\<times> v) \<^bold>+ (y \<^bold>\<times> w))" using \<open>y \<^bold>\<le> v \<^bold>+ w \<longrightarrow> y = y \<^bold>\<times> v \<^bold>+ y \<^bold>\<times> w\<close> by auto
            hence "C (y \<^bold>\<times> v) (y \<^bold>\<times> w)" using SC_def2 \<open>C x y \<and> SC x \<and> SC y\<close> by blast
            hence "C v (y \<^bold>\<times> w)" using E_def MTC PCP R T10 \<open>O v y \<and> O w y\<close> symmetry by blast
            thus "C v w" using E_def MTC PCP R T10 \<open>O v y \<and> O w y\<close> by blast
          qed
        next
          assume "\<not> (O v x \<and> O w x \<or> O v y \<and> O w y)"
          hence "x = w \<and> y = v \<or> x = v \<and> y = w" using another_funny_lemma  \<open>x \<^bold>+ y = v \<^bold>+ w\<close> by auto
          thus "C v w"
            using \<open>C x y \<and> SC x \<and> SC y\<close> symmetry by blast
        qed
      qed
    qed
  qed
  thus "SC (x \<^bold>+ y)" using SC_def2 by simp
qed

lemma (in MT) CimpliesCorEC: "C x y \<longleftrightarrow> (O x y \<or> EC x y)"
  using EC_def overlap_imnplies_connection by auto

lemma (in GEMTC) CimpliesOc:  "C x y \<longrightarrow> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)" nitpick oops

lemma (in GEMTC) "EC x y \<longrightarrow> (\<exists> y. IP y (\<^bold>\<not> x))" nitpick [user_axioms] oops

lemma (in GEMTC) ECimpliesOc: "((\<exists> z. IP z (\<^bold>\<not> x)) \<or> (\<exists> z. IP z (\<^bold>\<not> y))) \<longrightarrow> 
EC x y \<longrightarrow> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
proof 
  assume "(\<exists> z. IP z (\<^bold>\<not> x)) \<or> (\<exists> z. IP z (\<^bold>\<not> y))"
  thus "EC x y \<longrightarrow> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
  proof (rule disjE)
    assume "\<exists> z. IP z (\<^bold>\<not> x)"
    show "EC x y \<longrightarrow> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
    proof
      assume "EC x y"
      hence "x \<noteq> u" by (metis EC_def P.D_def T1 T34 T37 T51)
      hence "x \<noteq> u \<and> (\<exists> z. IP z (\<^bold>\<not> x))" using \<open>\<exists>z. IP z (\<^bold>\<not> x)\<close>..
      with closure_closure have "(\<exists> a. \<forall> y. P y a \<longleftrightarrow> \<not> O y (\<^bold>e x))"..
      then obtain a where a: "\<forall> y. P y a \<longleftrightarrow> \<not> O y (\<^bold>e x)"..
      with c_intro have "(\<^bold>c x) = a"..
      hence "O (\<^bold>c x) y" sorry
      thus "O x (c y) \<or> O (\<^bold>c x) y"..
    qed
   
  

lemma (in GEMT) "C x y \<longleftrightarrow> (O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))" nitpick oops

lemma (in GEMTC) "C x y \<longleftrightarrow> (O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))"
proof
  assume "C x y"
  show "O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
  proof
    cases
    assume "O x y"
    thus "O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"..
  next assume "\<not> O x y"
    hence "EC x y" using EC_def \<open>C x y\<close> by blast
    hence "(O x (\<^bold>c y) \<or> O (\<^bold>c x) y)" using ECimpliesOc by blast
    thus "(O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))"..
  qed
next
  assume "O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
  thus "C x y" 
  proof (rule disjE)
    assume "O x y"
    thus "C x y" by (simp add: overlap_imnplies_connection)
  next
    assume "(O x (\<^bold>c y) \<or> O (\<^bold>c x) y)"
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
          assume "O (\<^bold>c x) y"
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

  text {* As you've observed, the crucial problem with this proof is also proving the existence
of a connection, when we don't have an overlap. So I think we have the same underlying problem
with both proofs, and if we can find some examples in the literature, we'll be able to overcome it.
 *}


lemma (in GEMTC) "(\<exists> z. IP z x) \<and> (\<exists> z. IP z y) \<longrightarrow> EC x y \<longrightarrow> C z y \<and> \<not> C (\<^bold>i x) (\<^bold>i y)" oops

lemma (in GEMTC) "C x y \<longleftrightarrow> (O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))" oops

lemma (in GEMT) "x \<noteq> u \<and> (\<exists> z. IP z (\<^bold>\<not> x)) \<and> y \<noteq> u \<and> (\<exists> z. IP z (\<^bold>\<not> y)) \<longrightarrow>
 C x y \<longleftrightarrow> (O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))" sledgehammer oops

lemma (in GEMTC) "x \<noteq> u \<and> (\<exists> z. IP z (\<^bold>\<not> x)) \<and> y \<noteq> u \<and> (\<exists> z. IP z (\<^bold>\<not> y)) \<longrightarrow>
 C x y \<longleftrightarrow> (O x y \<or> (O x (\<^bold>c y) \<or> O (\<^bold>c x) y))" sledgehammer oops

  text {* The predicate SC is still too general to capture the desired notion of an integral whole-
a one-piece entity. On the other hand, one needs a stronger notion of connectedness, ruling out entities 
made up of pieces that are connected only externally, such as the sum of two balls barely touching
each other. In GEMTC, we may do so by requiring that also the entity's interior be self-connected: *}

definition SSC :: "i\<Rightarrow>bool" ("SSC")
  where
"SSC x \<equiv> SC x \<and> SC (\<^bold>i x) "

text {* On the other hand one would need some means for expressing the distinction between self connected 
entities in general  (such as the bottom half of a ball) and self-connected wholes (the entire ball)
. After all, we are interested in connected whole as significant case of unity-namely topological unity.
This means can be found in GEMTC by singling out those entities that are maximally strongly self-connected:
*}

definition MSSC :: "(i\<Rightarrow>bool)" ("MSSC")
  where
"MSSC x \<equiv> SSC x \<and> (\<forall>y. (SSC y \<and> O y x) \<longrightarrow> P y x)"

text {* Or, more generally, by singling out entities that are maximally strongly self-connected relative 
to some property or condition \<Phi>: *}



end
