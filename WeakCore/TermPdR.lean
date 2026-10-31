import WeakCore.TermFreeQW

/-! # TermPdR: the relaxed `Pδ` witness

`pd_witness` for TermMain's relaxed plant-transfer predicate: the piece-lowest own promise `t` of an
idle thread meets it after a thread step; the plant credit is asked only for a reading with a
resource (`g.R ≠ .zero`).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(Pδ R-split) The relaxed `Pδ` witness**: the piece-lowest own promise `t` of an idle thread
`j`, at a non-word unit of `j`'s own cell, carrying (only when `g.R ≠ .zero`) a key-free plant credit for the entry's payload on top of
its `PromCrK` credit before the step, meets the relaxed `Pδ g t` after it. -/
theorem pd_witnessR {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {g : TermPiece.GdE} {us : List Acc} {t : Ts} {m : Msg}
    (ht : t ∈ thj.promises) (hm : c.mem[t]? = some m) (hl : m.loc.label = g.l) (hus : accs g.S = some us)
    (hb1 : g.b ≤ m.loc.offset) (hb2 : m.loc.offset < g.b + nWords us)
    (hlow : ∀ t' m', t' ∈ thj.promises → c.mem[t']? = some m' → m'.loc.label = m.loc.label →
      g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t')
    {cl0 : Cell} (hcl0 : Eg.sto m.loc.label = some cl0) (ho0 : cl0.owner = some j)
    (hnw : ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j S0) m.loc)
    (hR : g.R ≠ .zero → ∃ S0 : AllocLabel → Prop,
      TermPlant.PromCrK (Cut Eg j S0) (stOf c.mem c.pairs thj) (cr j) (db j) ∧ ¬ WordUnit (Cut Eg j S0) m.loc ∧
      PlantCr (Cut Eg j S0) (stOf c.mem c.pairs thj) m t g.R ∧ TermPlant.CrKeys g.R) :
    t ∉ th.promises ∧ ∃ j' thj' m', j' ≠ i ∧ c.ths[j']? = some thj' ∧ t ∈ thj'.promises ∧
      c'.mem[t]? = some m' ∧ m'.loc.label = g.l ∧
      (∃ us', accs g.S = some us' ∧ g.b ≤ m'.loc.offset ∧ m'.loc.offset < g.b + nWords us' ∧
        (∀ t2 m2, t2 ∈ thj'.promises → c'.mem[t2]? = some m2 → m2.loc.label = m'.loc.label →
          g.b ≤ m2.loc.offset → m2.loc.offset < g.b + nWords us' → t ≤ t2) ∧
        (∃ cl1, Eg.sto m'.loc.label = some cl1 ∧ cl1.owner = some j') ∧
        ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j' S0) m'.loc) ∧
      (g.R ≠ .zero → ∀ (Sj : AllocLabel → Prop) thj'', c'.ths[j']? = some thj'' →
        PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j' Sj) (stOf c'.mem c'.pairs thj'')
          m' t (cr j' t + g.R) ∧ TermPlant.CrKeys (cr j' t + g.R)) := by
  have hpre := tctx_pre X
  have hm' : c'.mem[t]? = some m := by rw [hpre t (X.inv.plt j thj t hj ht)]; exact hm
  refine ⟨fun hti => X.inv.disj j i thj th t hji hj X.hth ht hti, j, thj, m, hji, hj, ht, hm', hl,
    ⟨us, hus, hb1, hb2, fun t2 m2 ht2 hm2 hl2 h1 h2 => ?_, ⟨cl0, hcl0, ho0⟩, hnw⟩, fun hR0 Sj thj'' hj'' => ?_⟩
  · have hm2' : c.mem[t2]? = some m2 := by rw [← hpre t2 (X.inv.plt j thj t2 hj ht2)]; exact hm2
    exact hlow t2 m2 ht2 hm2' hl2 h1 h2
  · obtain ⟨S0, hC, hw, hpc, hK⟩ := hR hR0
    obtain ⟨hP2, hK2⟩ := plantCrK_add hC ht hm hw hpc hK
    have e : thj'' = thj := Option.some.inj (hj''.symm.trans ((X.ho _ hji).trans hj))
    subst e
    exact ⟨plantCr_post (Sj := Sj) X Y Z hji hj hP2, hK2⟩

#print axioms pd_witnessR

/-- **`hpredNU`'s Yes-half from `UndefLowG`**: at a single-word unit `o` (a one-unit solid piece), a
defined message below `tw` makes the word before `tw` defined. -/
theorem predNU_of_UL {mem : Memory} {l : AllocLabel} {cl : Cell} {o : Nat} {tw : Ts} {U : Ty}
    (hUL : ∀ (o : Nat) (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 → mem[t1]? = some m1 → mem[t2]? = some m2 →
      m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ → (∃ b U us i, TermPiece.Piece cl.ty b U ∧ accs U = some us ∧ b ≤ o ∧
        InAcc us i (o - b) ∧ ∀ o2, InAcc us i o2 → o2 = o - b) →
      m1.val ≠ .undef → m2.val ≠ .undef)
    (hat : AtOff cl.ty o U) (hsol : Solid U) (hU : accs U = some [Acc.one])
    (hex : ∃ t0 m0, t0 < tw ∧ mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef) :
    ∃ w, PredAt mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef := by
  obtain ⟨t0, m0, hlt, hm0, hl0, hnu⟩ := hex
  obtain ⟨t1, m1, ht1, hpred, -, hm1, hl1⟩ := predAt_above (tw - t0) t0 m0 rfl hlt hm0 hl0
  refine ⟨mw m1, hpred, ?_⟩
  show m1.val ≠ .undef
  rcases Nat.lt_or_ge t0 t1 with h | h
  · have hP : TermPiece.Piece cl.ty o U := ⟨hat, hsol, by rw [wc_of_accs hU]; decide⟩
    refine hUL o t0 t1 m0 m1 h hm0 hm1 hl0 hl1 ⟨o, U, [Acc.one], 0, hP, hU, Nat.le_refl o, ?_, ?_⟩ hnu
    · rw [Nat.sub_self]; exact ⟨by simp [nWords], by simp [nWords, Acc.size]⟩
    · intro o2 h2
      rw [Nat.sub_self]
      exact inAcc_one h2
  · have e : t1 = t0 := Nat.le_antisymm h ht1
    subst e
    rw [hm0] at hm1
    cases hm1
    exact hnu

#print axioms predNU_of_UL

/-- **`foreign_overCrNPO` with `hpredNU` discharged** from `UndefLowG` (`predNU_of_UL`). -/
theorem foreign_overCrNPOU {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    (hOC : TermOverCr.OverCrG Eg c cr)
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
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
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
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl :=
  foreign_overCrNPG hsc X Y (Z.toC _ _ _ _ _) hm hnps hOC hji hj hc2 hown hpf2 hnd hTlab hT hTp hD hwaD hPA
    (fun _ _ _ _ _ _ _ _ _ hat hsol hU hex => predNU_of_UL hUL hat hsol hU hex)

#print axioms foreign_overCrNPOU

/-- **(iii′) `htg_pre` at the piece-lowest own promise**: the window bound is the lowest own promise
`t0` of the entry's piece, and the footprint condition is asked at `t0` only (`hFpT0`), not
label-wide at a guarded unit (`WinGL`). -/
theorem htg_preT0 {E : TEnv} {s : St} {cr db : Ts → Res} {l : AllocLabel} {c : Cell} {g : TermPiece.GdE}
    {us : List Acc} {o : Nat} {tw : Ts}
    (hC : TermPlant.PromCrK E s cr db)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : TermPiece.Piece c.ty g.b g.S) (hus : accs g.S = some us)
    (hnw : ∀ o', g.b ≤ o' → o' < g.b + nWords us → ¬ WordUnit E ⟨l, o'⟩)
    (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (h1 : g.b ≤ o) (h2 : o < g.b + nWords us)
    -- OPEN (iii′): the footprint promises at `l` lie above the piece-lowest own promise
    (hFpT0 : ∀ t0 m0, t0 ∈ s.promises → s.mem[t0]? = some m0 → m0.loc.label = l → g.b ≤ m0.loc.offset →
      m0.loc.offset < g.b + nWords us →
      (∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = l → g.b ≤ m'.loc.offset →
        m'.loc.offset < g.b + nWords us → t0 ≤ t') →
      ∀ tf mf, tf ∈ FpAt E ⟨l, 0⟩ → s.mem[tf]? = some mf → mf.loc.label = l → t0 < tf)
    (hwl : g.ws.length = nWords us) (hv : ValOfR E g.S g.ws g.R) (hK : TermPlant.CrKeys g.R) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us ∧ t ≤ tw ∧
      PlantCr E s m t (cr t + g.R) ∧ TermPlant.CrKeys (cr t + g.R) := by
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := hl
  have hlw : mw.loc.label = l := by rw [hml]
  have ho : mw.loc.offset = o := by rw [hml]
  obtain ⟨t0, m0, ht0, hm0, hl0, hb0, ho0, hle, hmin⟩ := lowest_in_piece htw hmw hlw
    (by rw [ho]; exact h1) (by rw [ho]; exact h2)
  obtain ⟨t, m, ht, hm, hlt, hb1, hb2, hle2, hpc, hk⟩ := pd_pre hC hsto hown hpf hlay hP hus hnw ht0 hm0 hl0
    hb0 ho0 (Nat.le_refl _) (lt_size_of_some hm0) (hFpT0 t0 m0 ht0 hm0 hl0 hb0 ho0 hmin) hwl hv hK
  exact ⟨t, m, ht, hm, hlt, hb1, hb2, Nat.le_trans hle2 hle, hpc, hk⟩

#print axioms htg_preT0

/-! ## `noOR` along `AtOff` (for `dn_items`' `noOR g.S`) -/

theorem noOR_shiftTR : ∀ (t : Ty) (c : Nat), noOR (t.shiftT c) = noOR t := by
  intro t
  induction t with
  | tvar k => intro c; simp only [Ty.shiftT]; split <;> rfl
  | prod a b iha ihb => intro c; simp [Ty.shiftT, noOR, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftT, noOR, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftT, noOR, ih]
  | ptr μ t _ => intro c; cases μ <;> rfl
  | ptrOpt μ t _ => intro c; cases μ <;> rfl
  | loc μ t _ => intro c; cases μ <;> rfl
  | mu t ih => intro c; simp [Ty.shiftT, noOR, ih]
  | tex κ t ih => intro c; simp [Ty.shiftT, noOR, ih]
  | iall t ih => intro c; simp [Ty.shiftT, noOR, ih]
  | iex t ih => intro c; simp [Ty.shiftT, noOR, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftT, noOR, ih]
  | _ => intro c; rfl

theorem noOR_shiftIR : ∀ (t : Ty) (c : Nat), noOR (t.shiftI c) = noOR t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp [Ty.shiftI, noOR, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftI, noOR, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftI, noOR, ih]
  | ptr μ t _ => intro c; cases μ <;> rfl
  | ptrOpt μ t _ => intro c; cases μ <;> rfl
  | loc μ t _ => intro c; cases μ <;> rfl
  | mu t ih => intro c; simp [Ty.shiftI, noOR, ih]
  | tex κ t ih => intro c; simp [Ty.shiftI, noOR, ih]
  | iall t ih => intro c; simp [Ty.shiftI, noOR, ih]
  | iex t ih => intro c; simp [Ty.shiftI, noOR, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftI, noOR, ih]
  | _ => intro c; rfl

theorem noOR_substTR : ∀ (t : Ty) (j : Nat) (s : Ty), noOR s = true → noOR t = true →
    noOR (Ty.substT j s t) = true := by
  intro t
  induction t with
  | tvar k =>
    intro j s hs _
    simp only [Ty.substT]
    split
    · exact hs
    · split <;> rfl
  | prod a b iha ihb =>
    intro j s hs h; simp only [Ty.substT, noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | sum a b iha ihb =>
    intro j s hs h; simp only [Ty.substT, noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | array i t ih => intro j s hs h; exact ih j s hs h
  | ptr μ t _ => intro j s _ h; cases μ <;> exact h
  | ptrOpt μ t _ => intro j s _ h; cases μ <;> exact h
  | loc μ t _ => intro j s _ h; cases μ <;> exact h
  | mu t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [noOR_shiftTR]; exact hs) h
  | tex κ t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [noOR_shiftTR]; exact hs) h
  | iall t ih => intro j s hs h; exact ih j (s.shiftI 0) (by rw [noOR_shiftIR]; exact hs) h
  | iex t ih => intro j s hs h; exact ih j (s.shiftI 0) (by rw [noOR_shiftIR]; exact hs) h
  | refine t ψ ih => intro j s hs h; exact ih j s hs h
  | _ => intro j s _ _; rfl

theorem noOR_of_substTR : ∀ (t : Ty) (j : Nat) (s : Ty), noOR (Ty.substT j s t) = true → noOR t = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro j s h; simp only [Ty.substT, noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha j s h.1, ihb j s h.2⟩
  | sum a b iha ihb =>
    intro j s h; simp only [Ty.substT, noOR, Bool.and_eq_true] at h ⊢; exact ⟨iha j s h.1, ihb j s h.2⟩
  | array i t ih => intro j s h; exact ih j s h
  | ptr μ t _ => intro j s h; cases μ <;> exact h
  | ptrOpt μ t _ => intro j s h; cases μ <;> exact h
  | loc μ t _ => intro j s h; cases μ <;> exact h
  | mu t ih => intro j s h; exact ih (j + 1) _ h
  | tex κ t ih => intro j s h; exact ih (j + 1) _ h
  | iall t ih => intro j s h; exact ih j _ h
  | iex t ih => intro j s h; exact ih j _ h
  | refine t ψ ih => intro j s h; exact ih j s h
  | _ => intro j s _; rfl

theorem noOR_unfoldR {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : noOR (cl ρ W 0 0 (.mu s)) = true) : noOR (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold1 hW, cl_mu_eq]
  rw [cl_mu_eq] at h
  exact noOR_substTR _ 0 _ h (by simp only [noOR] at h; exact h)

theorem noOR_foldR {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : noOR (cl ρ W 0 0 (unfold1 (.mu s))) = true) : noOR (cl ρ W 0 0 (.mu s)) = true := by
  rw [cl_unfold1 hW, cl_mu_eq] at h
  rw [cl_mu_eq]
  simp only [unfold1] at h
  simp only [noOR]
  exact noOR_of_substTR _ 0 _ h

/-- **Every `AtOff` component of a type without non-`pub` references has none.** -/
theorem noOR_atOffR {U V : Ty} {d : Nat} (h : AtOff U d V) (hU : noOR U = true) : noOR V = true := by
  induction h with
  | here _ => exact hU
  | fst _ ih => simp only [noOR, Bool.and_eq_true] at hU; exact ih hU.1
  | snd _ _ ih => simp only [noOR, Bool.and_eq_true] at hU; exact ih hU.2
  | elem _ _ _ ih => exact ih hU
  | mu hW _ _ ih => exact ih (noOR_unfoldR hW hU)
  | fold hW _ _ _ ih => exact noOR_foldR hW (ih hU)

#print axioms noOR_atOffR

/-- (hWbR route (iii)) `foreign_overCrCfg1PV` at `HWbRUp`. -/
theorem foreign_overCrCfg1PVG {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    {cv : Nat → Ts → Res}
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
    -- OPEN (hWbR route (iii), the `hWbRUp_of`)
    (hUp : TermFreeQW.HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cv j thj Sj l cl) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, -, -, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hstok : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hs, Or.inr ⟨f, hf⟩⟩
  have hpreM := tctx_pre X
  -- the targets at `l` are the owner's
  have hPj : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, t ∈ thj.promises ∧ c'.mem[t]? = some m ∧
      c.mem[t]? = some m ∧ m.loc.label = g.l ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      ∀ S0 : AllocLabel → Prop, ¬ WordUnit (Cut Eg j S0) m.loc := by
    intro g hg hgl t ht
    obtain ⟨j0, thj0, m, hj0, ht0, hm, hml, us, hus, h1, h2, hlow, ⟨cl0, hcl0, ho0⟩, hnw⟩ := hPd g hg t ht
    rw [hml, hgl, hs] at hcl0
    have ho : cl.owner = some j0 := by rw [Option.some.inj hcl0]; exact ho0
    have ej : j = j0 := by rw [hown] at ho; exact Option.some.inj ho
    subst ej
    have e1 : thj = thj0 := Option.some.inj (hj.symm.trans hj0)
    subst e1
    have hmc : c.mem[t]? = some m := by rw [← hpreM t (X.inv.plt j thj t hj ht0)]; exact hm
    exact ⟨m, us, ht0, hm, hmc, hml, hus, h1, h2, hlow, hnw⟩
  have hPc : ∀ g ∈ Gd, g.l = l → TermPiece.Piece cl.ty g.b g.S := by
    intro g hg hgl
    obtain ⟨c1, hc1, -, -, hpc, -⟩ := hDrop.1 g hg
    rw [hgl, hstok] at hc1
    cases hc1
    exact hpc
  have hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l := by
    intro g hg t m ht hm
    obtain ⟨-, -, m0, -, -, hm0, hl0, -⟩ := hPd g hg t ht
    rw [hm] at hm0
    cases hm0
    exact hl0
  have hinj := tg_inj (E := Cut Eg i S) (s := stOf c'.mem c'.pairs thj) (tg := tg) (Gd := Gd)
    (fun g hg t ht => by
      obtain ⟨-, -, m, -, -, hm, hml, us, hus, h1, h2, -⟩ := hPd g hg t ht
      obtain ⟨c1, hc1, -, -, hpc, -⟩ := hDrop.1 g hg
      exact ⟨m, us, c1, hm, hml, hc1, hpc, hus, h1, h2⟩) hDrop.2
  obtain ⟨hDR, -, -⟩ := dnOf_facts (s := stOf c'.mem c'.pairs thj) (l := l)
    (Kf := kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) hinj hTlab hDrop.2
  obtain ⟨hD, hwaD⟩ := dn_items (k := i) (Sk := S) (cr := cv j) (δ := TermPlant.plantD1 Gd TermPiece.GdE.R tg)
    X.inv.proms hj X.hth ⟨f, hf⟩ hpf hpre_c (fun g hg hgl t ht => by
      obtain ⟨m, us, ht0, -, hmc, hml, hus, h1, h2, hlow, hnw⟩ := hPj g hg hgl t ht
      refine ⟨hDrop.1 g hg, noOR_atOffR (hPc g hg hgl).1 (X.inv.shty l cl ⟨f, hf⟩ hs), us, m, hus, hmc,
        by rw [hml]; exact hgl, ⟨ht0, ⟨m, hmc, rfl⟩, fun t' m' ht' hm' hl' => ?_⟩, hnw Sj, h1, h2⟩
      have hm'' : c'.mem[t']? = some m' := by rw [hpreM t' (X.inv.plt j thj t' hj ht')]; exact hm'
      exact hlow t' m' ht' hm'' (by rw [hl']) (by rw [hl']; exact h1) (by rw [hl']; exact h2)) hDR
  refine TermFreeQW.foreign_overCrCfg1WVG X Y Z hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hDrop.2 hTlab
    (fun g hg hgl t ht => ?_) (fun g hg hgl t ht => ?_) hD hwaD htgW1 hUL hUp
  · obtain ⟨m, us, -, hm, -, hml, hus, h1, h2, hlow, -⟩ := hPj g hg hgl t ht
    exact ⟨m, us, hm, hml, hlow, hPc g hg hgl, hus, h1, h2⟩
  · obtain ⟨m, us, ht0, -⟩ := hPj g hg hgl t ht
    exact ht0

#print axioms foreign_overCrCfg1PVG

/-- **`foreign_overCrCfg1W` from the relaxed `Pδ`**: the target facts `hTlab`, `hT`, `hTp` and the new
items' credit `hD`, `hwaD` (`dn_items`) come from the store's drop list (`Drop`, at the stepper's cut)
and the relaxed `Pδ` at each target (owner's piece-lowest promise at a non-word unit of its own
cell).  Left: `htgW1`, `hUL`, `hWbR`. -/
theorem foreign_overCrCfg1P {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hOC : TermOverCr.OverCrG Eg c cr)
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
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us →
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
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  exact foreign_overCrCfg1PVG X Y (Z.toC _ _ _ _ _) hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hDrop hPd
    (fun g hg hgl o tw hl hw _ => htgW1 g hg hgl o tw hl hw) hUL (TermFreeQW.hWbRUp_of_hWbR X Y (Z.toC _ _ _ _ _) hOC hji hj hc2 hown hpf2 hWbR)

#print axioms foreign_overCrCfg1P

end

end TermOverCrW
