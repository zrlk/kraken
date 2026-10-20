import WeakCore.TermK2aMem

/-! # TermFulCntR: the corrected staging `FulCntR` and the (M)-step lemmas over it

`TermK2a.FulCnt` is false as stated (niche-sum `pubWords` re-encodes the word: `decodeArm .niche`
resets the generation).  `FulCntR` asks only for a word of `pubWords rt ws`
naming the same label with the same `rts`, which is all `fulCnt_le` uses (via `EnvRts`).
-/

namespace TermK2a
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Staging (corrected `FulCnt`)**: same premises as `FulCnt`; the conclusion only asks for a
pub-position word of the binding that names the same label with the same `rts`. -/
def FulCntR (p : Prog) : Prop :=
  ∀ (E : TEnv) (sto : Sto) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (x : String) (rt : Ty)
    (ws : List Word) (w : Word) (m : Msg) (cl : Cell) (a : AllocLabel),
    (∀ l c, E.sto l = some c → sto l = some c) → ThInvE p E th → MemInv g E (stOf mem pairs th) →
    TermNoFul.WriteFrom g mem pairs th x rt ws w m.loc → m.val = w.val → Names a w →
    sto m.loc.label = some cl → NotSnd cl.ty m.loc.offset → CntOK cl.ty m.loc.offset (mw m) →
    ∃ w' ∈ pubWords rt ws, Names a w' ∧ w'.rts = w.rts

/-- `FulCnt` (if it held) gives `FulCntR`. -/
theorem fulCntR_of_fulCnt {p : Prog} (h : FulCnt p) : FulCntR p := by
  intro E sto g mem pairs th x rt ws w m cl a h1 hT hm hW hv hn hcl hns hc
  exact ⟨w, h E sto g mem pairs th x rt ws w m cl a h1 hT hm hW hv hn hcl hns hc, hn, rfl⟩

/-- A promise `u` fulfilled by a single-word write (`SWT`) at a counted single slot naming `a`:
`t ≤ u` under (R) at `t`. -/
theorem fulCnt_leR {p : Prog} {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh}
    {a : AllocLabel} {t u : Ts} {m : Msg} {cl : Cell}
    (hFC : FulCntR p) (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th)) (hRt : ThRts t a th)
    (hW : TermNoFul.SWT g mem pairs th m.loc m.val u)
    (hcl : sto m.loc.label = some cl) (hn : Names a (mw m))
    (hns : NotSnd cl.ty m.loc.offset) (hc : CntOK cl.ty m.loc.offset (mw m)) : t ≤ u := by
  obtain ⟨a', n, hv, ha'⟩ := hn
  have hv' : m.val = .loc a' n := hv
  rcases hW with ⟨y, op, e, hterm, hW | hW⟩ |
      ⟨acq, rel, wa, ee, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, hterm, e1, e2, e3, hb, hval, hrts⟩
  · obtain ⟨pw, b, rel, us, ws, j, w, hU, hj, hwj, hl, hval, hrts⟩ := hW
    have hwv : w.val = .loc a' n := by rw [← hval]; exact hv'
    have hnames : Names a w := ⟨a', n, hwv, ha'⟩
    have hwm : w ∈ ws := List.mem_of_getElem? hwj
    obtain ⟨x, rt, hdv, hx⟩ := TermNoFul.unitsOp_var hU hwm hnames
    have hcw := hFC E sto g mem pairs th x rt ws w m cl a h1 hT hm
      ⟨hx, hwm, Or.inl ⟨y, op, e, pw, b, rel, us, j, hterm, hdv, hU, hj, hwj, hl⟩⟩ hval hnames hcl hns hc
    obtain ⟨w', hw', hn', hr'⟩ := hcw
    have hle := hRt.1 x rt ws (TermNoFul.lookupE_mem hx) w' hw' hn'
    rw [hr'] at hle
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle (hrts hk a' n hwv))
  · obtain ⟨o, -, -, -, -, -, mr, nw, hval⟩ := hW
    rw [hval] at hv'
    exact absurd hv' (TermNoFul.fetch_notLoc o mr nw a' n)
  · have hnv : nw.val = .loc a' n := by rw [← hval]; exact hv'
    have hnames : Names a nw := ⟨a', n, hnv, ha'⟩
    obtain ⟨x, rfl, hx⟩ := TermNoFul.evalAt_names e3 (List.mem_singleton_self nw) hnames
    have hcw := hFC E sto g mem pairs th x t3 [nw] nw m cl a h1 hT hm
      ⟨hx, List.mem_singleton_self nw, Or.inr ⟨acq, rel, wa, ee, tn, ok, fail, t1, t2, pw, ew, hterm, rfl,
        e1, e2, hb⟩⟩ hval hnames hcl hns hc
    obtain ⟨w', hw', hn', hr'⟩ := hcw
    have hle := hRt.1 x t3 [nw] (TermNoFul.lookupE_mem hx) w' hw' hn'
    rw [hr'] at hle
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hle (hrts hk a' n hnv))

/-- **`MemRtsC` across an owner step** at a fixed `t` (the old `tmin`, with (R) at `t`). -/
theorem memRtsC_stepR {p : Prog} {g : G} {E E' : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {a : AllocLabel} {t : Ts} {r : Memory × List Ts × TTh}
    (hFC : FulCntR p) (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (h4 : ∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th)) (hr : r ∈ tstep g mem pairs th)
    (hF : Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (ht : tminOf sto (stOf mem pairs th) a = some t) (hRt : ThRts t a th)
    (hC : MemRtsC sto t a mem pairs th.promises) :
    MemRtsC sto' t a r.1 r.2.1 r.2.2.promises := by
  have hlt : ∀ u ∈ th.promises, u < mem.size := hm.2.2.1
  have hpp := MemInv_nopair hm
  have hPO : PromOK (stOf mem pairs th) := hm.2.2.2.2.2.2.2.2.2.2
  have htlt : t < mem.size := hlt t (tminOf_spec ht).1
  have hext : MemExt mem r.1 := (tstep_appUp hr).2.1
  have hgrow := TermFul.tstep_grow hr
  obtain ⟨-, rem⟩ := TermNoFul.tstep_fulT hlt hpp hr
  intro u m cl hmu hnP hcl hn hslot
  rcases Nat.lt_or_ge u mem.size with hus | hus
  · have hmu0 : mem[u]? = some m := TermFul.memExt_back hext hus hmu
    have hpair : ∀ (v : Nat) m0, v + 1 = u → v ∈ r.2.1 → r.1[v]? = some m0 → v ∈ pairs ∧ mem[v]? = some m0 := by
      intro v m0 hv hvp hv0
      have hvs : v < mem.size := by omega
      refine ⟨?_, TermFul.memExt_back hext hvs hv0⟩
      rcases hgrow.2 v hvp with h | h
      · exact h
      · omega
    by_cases hup : u ∈ th.promises
    · obtain ⟨m2, hm2, hW⟩ := rem u hup hnP
      have e : m2 = m := Option.some.inj (hm2.symm.trans hmu0)
      subst e
      rcases hslot with ⟨hns, hc⟩ | ⟨v, m0, hv, hvp, hv0, -, -⟩
      · exact fulCnt_leR hFC hk (fun l c h => h3 l c (h1 l c h)) hT hm hRt hW hcl hn hns hc
      · obtain ⟨hvp', -⟩ := hpair v m0 hv hvp hv0
        exact absurd hv.symm (hPO.2.2 u hup v hvp')
    · have hcl0 : sto m.loc.label = some cl := by
        cases e : sto m.loc.label with
        | some c0 => rw [h3 _ _ e] at hcl; rw [hcl]
        | none =>
          exfalso
          obtain ⟨hEn, hE'⟩ := h4 _ _ hcl e
          rcases hF.1.2.2.1 m.loc.label with h | ⟨⟨j, hj, -, hl⟩, -⟩
          · rw [h, hEn] at hE'; cases hE'
          · exact hup ((hm.2.2.2.1.1 j hj).2.1 u m hmu0 hl)
      refine hC u m cl hmu0 hup hcl0 hn ?_
      rcases hslot with h | ⟨v, m0, hv, hvp, hv0, hlab, hcp⟩
      · exact .inl h
      · obtain ⟨hvp', hv0'⟩ := hpair v m0 hv hvp hv0
        exact .inr ⟨v, m0, hv, hvp', hv0', hlab, hcp⟩
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htlt hus)

/-- **The `PtrRtsThreadGL` `MemRtsC` conjunct**: `MemRtsC` at every new `tmin` (the old one,
`tminOf_step`), from `MemRtsC` at every old `tmin` and (R) from `PtrRtsE`. -/
theorem memRtsC_stepGLR {p : Prog} {g : G} {E E' : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {a : AllocLabel} {r : Memory × List Ts × TTh}
    (hFC : FulCntR p) (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (h4 : ∀ l c, sto' l = some c → sto l = none → E.sto l = none ∧ E'.sto l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th))
    (hR : PtrRtsE sto (stOf mem pairs th) th a) (hnp : ¬ PubAt th a)
    (hr : r ∈ tstep g mem pairs th) (hF : Foot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none)
    (hC : ∀ t, tminOf sto (stOf mem pairs th) a = some t → MemRtsC sto t a mem pairs th.promises) :
    ∀ t, tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t → MemRtsC sto' t a r.1 r.2.1 r.2.2.promises := by
  intro t ht
  rw [tminOf_step hk h1 h3 hT hm hR hnp hr hNF] at ht
  exact memRtsC_stepR hFC hk h1 h3 h4 hT hm hr hF ht (hR t ht).2 (hC t ht)

end TermK2a

#print axioms TermK2a.fulCntR_of_fulCnt
#print axioms TermK2a.fulCnt_leR
#print axioms TermK2a.memRtsC_stepR
#print axioms TermK2a.memRtsC_stepGLR
