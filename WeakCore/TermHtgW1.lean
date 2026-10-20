import WeakCore.TermOverCrPoolF

/-! # TermHtgW1: the drop targets exist (`htgW1` supplier)

The pool route's target predicate `Pδ0` (TermMain's plant-transfer `Pδ` without its `g.R ≠ 0`
clause): a foreign promise `t` of an idle thread `j`, the lowest of `j`'s promises in the
entry's piece, at a non-word unit of `j`'s own cell.

`htgW1_sup`: at a guarded entry `g` of the drop list, at a non-word unit `o` of `g`'s piece
holding `j`'s lowest promise `tw`, the target choice `tgIn η.fp Pδ0` finds a target (`htgW1`
with the `¬ WordUnit` premise, the amended `HtgW1At`).  `hPd_sup`: what a found target is
(`HPd`).  The witness is `j`'s lowest promise in the piece (`lowest_in_piece`); it sits at a
non-word unit since a word component meeting the piece is the piece (`piece_match`).
-/

namespace TermHtgW1
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermOverCrW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The pool route's plant-transfer target predicate (TermMain `Pδ` without the `g.R ≠ 0`
clause). -/
def Pδ0 (c c' : Cfg) (Eg : GEnv) (i : Nat) (th : TTh) : TermPiece.GdE → Ts → Prop :=
  fun g t => t ∉ th.promises ∧
    ∃ j thj m, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧ c'.mem[t]? = some m ∧
      m.loc.label = g.l ∧ (∃ us, accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us ∧
        (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
          g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
        (∃ cl, Eg.sto m.loc.label = some cl ∧ cl.owner = some j) ∧
        ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j S0) m.loc)

theorem accs_word {r : Idx} {P : Proto} (hg : P.ghost = false) : accs (.word r P) = some [.one] := by
  simp [accs, hg]

theorem accs_word2 {r : Idx} {P : Proto2} : accs (.word2 r P) = some [.two] := rfl

/-- **Word units of a piece**: a piece meeting a word unit is that word (two-word) component,
so all its units are word units or none is. -/
theorem nw_piece {E : TEnv} {l : AllocLabel} {cl : Cell} (hsto : E.sto l = some cl) {b : Nat} {S : Ty}
    {us : List Acc} (hP : TermPiece.Piece cl.ty b S) (hus : accs S = some us) {o o' : Nat}
    (h1 : b ≤ o) (h2 : o < b + nWords us) (h1' : b ≤ o') (h2' : o' < b + nWords us)
    (hno : ¬ WordUnit E ⟨l, o⟩) : ¬ WordUnit E ⟨l, o'⟩ := by
  rintro ⟨c, hc, h⟩
  have hc' : c = cl := Option.some.inj (hc.symm.trans hsto)
  subst hc'
  have hwS := wc_of_accs hus
  rcases h with ⟨r, P, hg, hat⟩ | ⟨r, P, hat⟩ | ⟨r, P, hge, hat⟩
  · have hu1 := accs_word (r := r) hg
    have hp' : TermPiece.Piece c.ty o' (.word r P) :=
      ⟨hat, Solid_word r P, by rw [wc_of_accs hu1]; simp [nWords, Acc.size]⟩
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hp' hwS (wc_of_accs hu1) h1' h2' (Nat.le_refl _)
      (by simp [nWords, Acc.size])
    subst e1 e2
    rw [hus] at hu1
    cases hu1
    have : o = b := by simp [nWords, Acc.size] at h2; omega
    subst this
    exact hno ⟨c, hsto, Or.inl ⟨r, P, hg, hat⟩⟩
  · have hu2 := accs_word2 (r := r) (P := P)
    have hp' : TermPiece.Piece c.ty o' (.word2 r P) :=
      ⟨hat, Solid_word2 r P, by rw [wc_of_accs hu2]; simp [nWords, Acc.size]⟩
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hp' hwS (wc_of_accs hu2) h1' h2' (Nat.le_refl _)
      (by simp [nWords, Acc.size])
    subst e1 e2
    rw [hus] at hu2
    cases hu2
    simp [nWords, Acc.size] at h2
    by_cases e : o = b
    · subst e; exact hno ⟨c, hsto, Or.inr (Or.inl ⟨r, P, hat⟩)⟩
    · exact hno ⟨c, hsto, Or.inr (Or.inr ⟨r, P, by show 1 ≤ o; omega,
        by show AtOff c.ty (o - 1) _; rw [show o - 1 = b by omega]; exact hat⟩)⟩
  · have hu2 := accs_word2 (r := r) (P := P)
    have hp' : TermPiece.Piece c.ty (o' - 1) (.word2 r P) :=
      ⟨hat, Solid_word2 r P, by rw [wc_of_accs hu2]; simp [nWords, Acc.size]⟩
    have hge' : 1 ≤ o' := hge
    obtain ⟨e1, e2⟩ := TermPiece.piece_match hP hp' hwS (wc_of_accs hu2) h1' h2' (by omega)
      (by simp [nWords, Acc.size]; omega)
    subst e2
    rw [hus] at hu2
    cases hu2
    simp [nWords, Acc.size] at h2
    rw [← e1] at hat
    by_cases e : o = b
    · subst e; exact hno ⟨c, hsto, Or.inr (Or.inl ⟨r, P, hat⟩)⟩
    · exact hno ⟨c, hsto, Or.inr (Or.inr ⟨r, P, by show 1 ≤ o; omega,
        by show AtOff c.ty (o - 1) _; rw [show o - 1 = b by omega]; exact hat⟩)⟩

#print axioms nw_piece

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`htgW1` supplier** (the amended `HtgW1At`, at the target choice `tgIn η.fp Pδ0`). -/
theorem htgW1_sup {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hDr : TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) :
    ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) →
      ∃ t, TermPlant.tgIn η.fp (Pδ0 c c' Eg i th) g = some t := by
  intro g hg hgl o tw hl hnw us hus h1 h2 _
  obtain ⟨hpre_c, hs, -⟩ := own_agree (gfoot_of X Y Z) (X.inv.gfresh X.hth r.2.2.nalloc) hji Sj hc2 hown
  obtain ⟨c1, hc1, -, -, hP1, -⟩ := hDr.1 g hg
  have hc1' : cutSto Eg i l = some c1 := by
    have := hc1; rw [Y.1, hgl] at this; exact this
  have e : c1 = cl := Option.some.inj ((cutSto_some.1 hc1').1.symm.trans hs)
  subst e
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := hl
  obtain ⟨t, m, ht, hm, hlab, hb1, hb2, -, hmin⟩ := lowest_in_piece (s := stOf c.mem c.pairs thj) (l := l)
    (lo := g.b) (hi := g.b + nWords us) htw hmw (by rw [hml]) (by rw [hml]; exact h1) (by rw [hml]; exact h2)
  have hlt : t < c.mem.size := X.inv.plt j thj t hj ht
  refine tgIn_isSome (t := t) ?_ ⟨fun h => X.inv.disj j i thj th t hji hj X.hth ht h, j, thj, m, hji, hj, ht,
    by rw [tctx_pre X t hlt]; exact hm, by rw [hlab, hgl], us, hus, hb1, hb2, ?_, ⟨c1, by rw [hlab]; exact hs, hown⟩,
    ?_⟩
  · show t ∈ (CE η).fp
    rw [Y.1]
    exact mem_cut_fp_of_prom X.inv.proms X.inv.disj hji hj X.hth ht
  · intro t' m' ht' hm' hl' hb' hb''
    exact hmin t' m' ht' (by show c.mem[t']? = _; rw [← tctx_pre X t' (X.inv.plt j thj t' hj ht')]; exact hm')
      (by rw [hl', hlab]) hb' hb''
  · intro S0 hW
    have hW' : WordUnit (Cut Eg j S0) ⟨m.loc.label, m.loc.offset⟩ := hW
    rw [hlab] at hW'
    exact nw_piece (E := Cut Eg j S0) hpre_c hP1 hus h1 h2 hb1 hb2
      (fun h => hnw ((WordUnit_congr (E := Cut Eg j S0) (E' := Cut Eg j Sj) rfl).2 h)) hW'

#print axioms htgW1_sup

/-- **`HPd` at the target choice**: a found target is a `Pδ0` target. -/
theorem hPd_sup {c c' : Cfg} {Eg : GEnv} {i : Nat} {th : TTh} {F : List Ts} {Gd : List TermPiece.GdE} :
    ∀ g ∈ Gd, ∀ t, TermPlant.tgIn F (Pδ0 c c' Eg i th) g = some t → ∃ j0 thj0 m, c.ths[j0]? = some thj0 ∧
      t ∈ thj0.promises ∧ c'.mem[t]? = some m ∧ m.loc.label = g.l ∧ ∃ us, accs g.S = some us ∧
        g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us ∧
        (∀ t' m', t' ∈ thj0.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
          g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
        (∃ cl0, Eg.sto m.loc.label = some cl0 ∧ cl0.owner = some j0) ∧
        ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j0 S0) m.loc := by
  intro g _ t ht
  obtain ⟨-, -, j, thj, m, -, hj, htj, hm, hl, hrest⟩ := TermPlant.tgIn_spec ht
  exact ⟨j, thj, m, hj, htj, hm, hl, hrest⟩

#print axioms hPd_sup

end

end TermHtgW1
