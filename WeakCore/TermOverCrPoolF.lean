import WeakCore.TermPdR

/-! # TermOverCrPoolF: the foreign cover lemmas at the pool credits (Variant S)

Copies of `foreign_overCrCfgW`/`Cfg1W` (TermFreeQW) and `foreign_overCrNPOU`/`Cfg1P` (TermPdR) whose
cover hypothesis `hOC` and conclusion are at an arbitrary credit family `cv` (instantiated at
`TermPool.crPl cr pl`) instead of the `SysInvN` credits `cr`.  The proofs are unchanged.
-/

namespace TermFreeQW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermOverCrW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (pool) `foreign_overCrCfgW` with the cover clause at any credit family `cv` (`crPl cr pl`). -/
theorem foreign_overCrCfgWV {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbT-R): at a unit losing a footprint promise below its lowest own promise, the piece is
    -- resource-free and copyable, or the window transports back
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfgWVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    htgW hUL (hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)


#print axioms TermFreeQW.foreign_overCrCfgWV


/-- (pool) `foreign_overCrCfg1W` with the cover clause at any credit family `cv` (`crPl cr pl`). -/
theorem foreign_overCrCfg1WV {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    -- the store's footprint, coverage and mask export (`PubShape` branch)
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ →
      m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbT-R): at a unit losing a footprint promise below its lowest own promise, the piece is
    -- resource-free and copyable, or the window transports back
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfg1WVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hnd hTlab hT hTp hD hwaD
    htgW1 hUL (hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)


#print axioms TermFreeQW.foreign_overCrCfg1WV


end

end TermFreeQW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (pool) `foreign_overCrNPOU` with the cover clause at any credit family `cv` (`crPl cr pl`). -/
theorem foreign_overCrNPOUV {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- every thread's promises lie above its coherence (the `SysInvN` clause `PromAboveG`)
    (hPA : TermOverCr.PromAboveG c)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl :=
  foreign_overCrNPG hsc X Y Z hm hnps hOC hji hj hc2 hown hpf2 hnd hTlab hT hTp hD hwaD hPA
    (fun _ _ _ _ _ _ _ _ _ hat hsol hU hex => predNU_of_UL hUL hat hsol hU hex)


#print axioms TermOverCrW.foreign_overCrNPOUV


/-- (pool) `foreign_overCrCfg1P` with the cover clause at any credit family `cv` (`crPl cr pl`). -/
theorem foreign_overCrCfg1PV {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {lt : AllocLabel} {ot n : Nat}
    (hTF : TermPiece.TgtFoot (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n)
    {L0 : Nat → Bool} (hcov : TermPiece.GdCovUL (Cut Eg i S) (stOf c.mem c.pairs th) Gd lt ot n L0)
    (hLT0 : TermPiece.GdLT0 (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) lt ot n L0)
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = lt → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis (Cut Eg i S) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ⟨lt, k⟩)
    -- the store's drop list (`TOut`'s `Drop`, at the stepper's cut)
    (hDrop : TermPiece.Drop (Cut Eg i S) (stOf c.mem c.pairs th) Gd)
    -- the relaxed `Pδ` at each target
    (hPd : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ j0 thj0 m, c.ths[j0]? = some thj0 ∧ t ∈ thj0.promises ∧
      c'.mem[t]? = some m ∧ m.loc.label = g.l ∧ ∃ us, accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
        m.loc.offset < g.b + nWords us ∧
        (∀ t' m', t' ∈ thj0.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
          g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
        (∃ cl0, Eg.sto m.loc.label = some cl0 ∧ cl0.owner = some j0) ∧
        ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j0 S0) m.loc)
    -- OPEN (htgW at one-word units): targets of guarded entries, off the entry's two-word units
    (htgW1 : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw →
      ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ → ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
      (AtOff cl.ty g.b g.S → ∀ jj, TwoAt us jj → o ≠ g.b + jj ∧ o ≠ g.b + jj + 1) → ∃ t, tg g = some t)
    -- (`UndefLowG`, at single-word units) no `undef` message above a defined one
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → c.mem[t1]? = some m1 → c.mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    -- OPEN (hWbT-R)
    (hWbR : ∀ o tw b U us, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) l o tw →
      (∃ t m, c'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ t ≤ tw ∧ t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧
        c.mem[t]? = some m) →
      TermPiece.Piece cl.ty b U → accs U = some us → b ≤ o → o < b + nWords us →
      (tb 0 U = true ∧ Ty.affine U = false) ∨ TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfg1PVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hDrop hPd
    htgW1 hUL (TermFreeQW.hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)


#print axioms TermOverCrW.foreign_overCrCfg1PV

end

end TermOverCrW
