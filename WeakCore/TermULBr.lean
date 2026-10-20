import WeakCore.TermPdR
import WeakCore.TermUndefLow

/-! # TermULBr: `UndefLowG` gives the `hUL` premise

`foreign_overCrCfg1P` / `TermFreeQW` ask `hUL` at a single-word unit of a solid piece of the cell;
`UndefLowG` states it at a single-word unit of the laid-out cell (`onePc_oneU`).
-/

namespace TermULBr
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The `hUL` bridge**: at a cell of `E_g` with a laid-out type. -/
theorem hUL_of {Eg : GEnv} {mem : Memory} (h : TermUndefLow.UndefLowG Eg mem) {l : AllocLabel} {cl : Cell}
    (hl : Eg.sto l = some cl) (hlay : LayT cl.ty) :
    ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → mem[t1]? = some m1 → mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef :=
  fun o t1 t2 m1 m2 hlt h1 h2 hl1 hl2 hpc =>
    h l cl hl o (TermUndefLow.onePc_oneU hlay hpc) t1 t2 m1 m2 hlt h1 h2 hl1 hl2

/-- The same at a cell of a cut of `E_g`. -/
theorem hUL_cut {Eg : GEnv} {mem : Memory} (h : TermUndefLow.UndefLowG Eg mem) {j : Nat}
    {S : AllocLabel → Prop} {l : AllocLabel} {cl : Cell} (hl : (Cut Eg j S).sto l = some cl) (hlay : LayT cl.ty) :
    ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → mem[t1]? = some m1 → mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef :=
  hUL_of h (cutSto_some.1 hl).1 hlay

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`hUL` at a foreign step** (the form `foreign_overCrCfg1P` / `foreign_overCrNPOU` ask), from
`UndefLowG` at the pre-state: the post cut's own frontier cell is `E_g`'s, laid out by `MemInv`. -/
theorem hUL_step {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hU : TermUndefLow.UndefLowG Eg c.mem)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none) :
    ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef := by
  have hgf := TermInterf.gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, -, -, hpfr2⟩ := TermOverCrW.own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  exact hUL_of hU hs hlay

end

end TermULBr

#print axioms TermULBr.hUL_of
#print axioms TermULBr.hUL_cut
#print axioms TermULBr.hUL_step
