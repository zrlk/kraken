import WeakCore.TermPlantAtT
import WeakCore.TermPlantAtF
import WeakCore.TermPlantAtN
import WeakCore.TermPtrRts
import WeakCore.TermWin
import WeakCore.TermCertScope
import WeakCore.TermNoFulRun

/-! # TermPlantAtI: preservation of the plant-index clause, gate-independent part

The body of `TermPlantAtT.PlantIdxG` at one owner `j` and one cell `l` (`IdxBody`) across the
four kinds of steps, stated against an arbitrary next global environment `Eg'` with the facts a
producer supplies (selector stability from the `TermPtrStab`, append-only memory, the
footprint list shrinking or gaining only new indices, coherence monotonicity, `FulCoh`):

* `idxBody_keep`: every step that leaves the selected edge in place (foreign thread step,
  owner thread step with the edge kept, foreign promise, owner promise without plant);
* `idxBody_plant`: the planting promise (the new message is the edge).

The outer gate (which owners/cells the clause covers) is left to the final clause statement.
Also `cfgCoh_run` (coherence views name messages along runs).
-/

namespace TermPlantAtI
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermLiveProps (CohAt CfgCoh)

/-- The body of the plant-index clause at owner `j` (state `th`) and cell `l`. -/
def IdxBody (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (Eg : GEnv) (c : Cfg) (j : Nat) (th : TTh)
    (l : AllocLabel) : Prop :=
  ∃ (t : Ts) (mP : Msg), tm Eg c j l = some t ∧ c.mem[t]? = some mP ∧
    t ∈ th.promises ∧ th.vs.vWr ≤ mP.view ∧
    (∀ u m, c.mem[u]? = some m → m.loc.label = l → u ≤ t → u ∈ th.promises ∨ u ≤ th.vs.coh m.loc) ∧
    (∀ u m, u ∈ Eg.fpOf j → c.mem[u]? = some m → m.loc.label = l → t < u)

/-- **The body across a step keeping the edge**: same selected edge, memory extended,
the edge still outstanding below `vWr`, fulfilled promises at or below coherence (`FulCoh`),
coherence monotone, footprint entries old or new. -/
theorem idxBody_keep {tm : GEnv → Cfg → Nat → AllocLabel → Option Ts} {Eg Eg' : GEnv} {c c' : Cfg}
    {j : Nat} {th th' : TTh} {l : AllocLabel}
    (h : IdxBody tm Eg c j th l)
    (htm : tm Eg' c' j l = tm Eg c j l)
    (hlt : ∀ u, u ∈ th.promises → u < c.mem.size)
    (hmem : ∀ u, u < c.mem.size → c'.mem[u]? = c.mem[u]?)
    (hkeep : ∀ t m, tm Eg c j l = some t → c.mem[t]? = some m → t ∈ th.promises → th.vs.vWr ≤ m.view →
      t ∈ th'.promises ∧ th'.vs.vWr ≤ m.view)
    (hful : ∀ u, u ∈ th.promises → u ∉ th'.promises → ∀ m, c.mem[u]? = some m → u ≤ th'.vs.coh m.loc)
    (hcoh : ∀ b, th.vs.coh b ≤ th'.vs.coh b)
    (hfp : ∀ u, u ∈ Eg'.fpOf j → u ∈ Eg.fpOf j ∨ c.mem.size ≤ u) :
    IdxBody tm Eg' c' j th' l := by
  obtain ⟨t, mP, htm0, hmP, htP, hle, hA, hB⟩ := h
  have htl : t < c.mem.size := hlt t htP
  obtain ⟨h1, h2⟩ := hkeep t mP htm0 hmP htP hle
  refine ⟨t, mP, by rw [htm]; exact htm0, by rw [hmem t htl]; exact hmP, h1, h2, ?_, ?_⟩
  · intro u m hm hl hut
    have hul : u < c.mem.size := Nat.lt_of_le_of_lt hut htl
    rw [hmem u hul] at hm
    rcases hA u m hm hl hut with hu | hu
    · by_cases hu' : u ∈ th'.promises
      · exact Or.inl hu'
      · exact Or.inr (hful u hu hu' m hm)
    · exact Or.inr (Nat.le_trans hu (hcoh _))
  · intro u m hu hm hl
    rcases hfp u hu with hu0 | hge
    · by_cases hul : u < c.mem.size
      · rw [hmem u hul] at hm
        exact hB u m hu0 hm hl
      · exact Nat.lt_of_lt_of_le htl (Nat.le_of_not_lt hul)
    · exact Nat.lt_of_lt_of_le htl hge

/-- **The body at the planting promise**: the new message (index `c.mem.size`, view `w`)
is the selected edge; before it, at the private cell `l`, non-promise messages lie at or below
coherence (`hpriv`), and no footprint message lies at `l` (`hfpl`, a private cell is not `Vis`). -/
theorem idxBody_plant {tm : GEnv → Cfg → Nat → AllocLabel → Option Ts} {Eg Eg' : GEnv} {c c' : Cfg}
    {j : Nat} {th th' : TTh} {l : AllocLabel} {a : Address} {v : WeakMem.Val} {w : Ts}
    (htm : tm Eg' c' j l = some c.mem.size)
    (hmem' : c'.mem = c.mem.push ⟨a, v, w⟩)
    (hP : th'.promises = th.promises ++ [c.mem.size]) (hvs : th'.vs = th.vs)
    (hv : th.vs.vWr ≤ w)
    (hpriv : ∀ u m, u ∉ th.promises → c.mem[u]? = some m → m.loc.label = l → u ≤ th.vs.coh m.loc)
    (hfp : ∀ u, u ∈ Eg'.fpOf j → u ∈ Eg.fpOf j)
    (hfplt : ∀ u, u ∈ Eg.fpOf j → u < c.mem.size)
    (hfpl : ∀ u m, u ∈ Eg.fpOf j → c.mem[u]? = some m → m.loc.label ≠ l) :
    IdxBody tm Eg' c' j th' l := by
  have hget : ∀ u, u < c.mem.size → c'.mem[u]? = c.mem[u]? := fun u hu => by
    rw [hmem', Array.getElem?_push]; simp [Nat.ne_of_lt hu]
  have hnew : c'.mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [hmem', Array.getElem?_push]; simp
  refine ⟨c.mem.size, ⟨a, v, w⟩, htm, hnew, by rw [hP]; exact List.mem_append_right _ (List.mem_singleton.2 rfl),
    by rw [hvs]; exact hv, ?_, ?_⟩
  · intro u m hm hl hu
    rcases Nat.lt_or_ge u c.mem.size with hul | hug
    · rw [hget u hul] at hm
      by_cases hup : u ∈ th.promises
      · exact Or.inl (by rw [hP]; exact List.mem_append_left _ hup)
      · exact Or.inr (by rw [hvs]; exact hpriv u m hup hm hl)
    · have e : u = c.mem.size := Nat.le_antisymm hu hug
      exact Or.inl (by rw [hP, e]; exact List.mem_append_right _ (List.mem_singleton.2 rfl))
  · intro u m hu hm hl
    have hu0 := hfp u hu
    have hul := hfplt u hu0
    rw [hget u hul] at hm
    exact absurd hl (hfpl u m hu0 hm)

/-- Coherence views name messages along runs. -/
theorem cfgCoh_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') (hc : CfgCoh c) : CfgCoh c' := by
  cases h with
  | thread i hs _ => exact (TermLiveProps.threadSteps_coh hs hc).1
  | prom i a v w _ hw _ => exact (TermLiveProps.promise_coh c i a v w hc).1

theorem cfgCoh_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg}
    (h : Steps p k arch c0 c) (h0 : CfgCoh c0) : CfgCoh c := by
  induction h with
  | refl _ => exact h0
  | step hs _ ih => exact ih (cfgCoh_step hs h0)

/-- A word a cell's type allows lies within the cell's words (`WordOK` → `CellOK_cover`). -/
theorem wordOK_lt {η : TEnv} {n : Nat} {T : Ty} {vals : List Word} {o : Nat} {w : Word}
    (hc : CellOK η n T vals) (hw : WordOK η T o w) : o < vals.length := by
  obtain ⟨b, S, ws, o', w0, hseg, hv, hws, -, ho⟩ := hw
  obtain ⟨L, hL⟩ : ∃ L, accs S = some L := by
    rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us, j, -, hus, -, -⟩
    · exact Option.ne_none_iff_exists'.mp hA
    · exact ⟨us, hus⟩
  have hlen : ws.length = nWords L := hv.2 L hL
  have hj : o' < nWords L := by
    rw [← hlen]
    rcases Nat.lt_or_ge o' ws.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hws; cases hws
  rw [← ho]
  exact CellOK_cover hc hseg hL hj

/-- (G2 for defined values) **At a private own cell, a non-promise defined message lies
at or below coherence**: `MemOKP` places it at a word of the cell, where `OwnOKPF` (no
frontier) makes every later message a promise. -/
theorem priv_le_coh_def {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    (hm : MemInv g E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l = none)
    {t : Ts} {m : Msg} (ht : t ∉ s.promises) (hmt : s.mem[t]? = some m) (hl : m.loc.label = l)
    (hv : m.val ≠ .undef) : t ≤ s.vs.coh m.loc := by
  have hsto' : E.sto m.loc.label = some c := by rw [hl]; exact hsto
  have hW : WordOK E c.ty m.loc.offset (mw m) :=
    (hm.1.1 t m c ht hmt hsto').resolve_left hv
  obtain ⟨vals, hcell, hlat⟩ := OwnOKPF_cellP hm.2.1 hsto hown hpf
  have hlt := wordOK_lt hcell hW
  have hL := hlat m.loc.offset (vals[m.loc.offset]'hlt) (List.getElem?_eq_getElem hlt)
  have he : (⟨l, m.loc.offset⟩ : Address) = m.loc := by
    cases hm0 : m.loc; rw [hm0] at hl; simp only at hl; subst hl; rfl
  rw [he] at hL
  exact Nat.le_of_not_lt fun h => ht (hL.2.2 t m h hmt rfl)

/-- (G2, staged for the `msgInCell_of`, named) A non-promise message at an own private cell
lies within the cell's words. -/
def MsgInCell (E : TEnv) (s : St) : Prop :=
  ∀ (t : Nat) (m : Msg) (c : Cell), t ∉ s.promises → s.mem[t]? = some m → E.sto m.loc.label = some c →
    c.owner = some E.tid → E.pfr m.loc.label = none → TermCohLe.InCell c.ty m.loc.offset

/-- (G2) **At a private own cell, every non-promise message lies at or below coherence**,
given `MsgInCell` for the placeholders. -/
theorem priv_le_coh {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    (hm : MemInv g E s) (hU : MsgInCell E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid)
    (hpf : E.pfr l = none) {t : Ts} {m : Msg} (ht : t ∉ s.promises) (hmt : s.mem[t]? = some m)
    (hl : m.loc.label = l) : t ≤ s.vs.coh m.loc := by
  by_cases hv : m.val = .undef
  · obtain ⟨vals, hcell, hlat⟩ := OwnOKPF_cellP hm.2.1 hsto hown hpf
    have hsto' : E.sto m.loc.label = some c := by rw [hl]; exact hsto
    have hpf' : E.pfr m.loc.label = none := by rw [hl]; exact hpf
    have hlt := (hU t m c ht hmt hsto' hown hpf').lt hcell
    have hL := hlat m.loc.offset (vals[m.loc.offset]'hlt) (List.getElem?_eq_getElem hlt)
    have he : (⟨l, m.loc.offset⟩ : Address) = m.loc := by
      cases hm0 : m.loc; rw [hm0] at hl; simp only at hl; subst hl; rfl
    rw [he] at hL
    exact Nat.le_of_not_lt fun h => ht (hL.2.2 t m h hmt rfl)
  · exact priv_le_coh_def hm hsto hown hpf ht hmt hl hv

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (A″) **The planting promise is below `vWr`**: from a typed start at the promised
configuration carrying the `PtrRtsE` with the new message as `tmin`, K-4 (`NoFulPlRun`, anchored at
`AnchR E0u E1 E1` with the window `hwin` at `(E0u, E1)`, the planted `CertWinP` instance) keeps it
outstanding along the certificate until `publish l`, and K-5 (`winLe_gen`) gives `vWr ≤ w`. -/
theorem plant_vWr {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hk : k.storeDepRts = true)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hCSP : TermCertScope.CertScopeP p k arch Sp Init MintOK c0)
    {E0u E1 : TEnv}
    (hwin : ∀ c2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      TermTyped.NoHoldPubA p k arch E0u E1 j c2)
    (hAn : TermTyped.AnchR E0u E1 E1
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }))
    {sto : TermPtrRts.Sto}
    (hs1 : ∀ l c, E1.sto l = some c → sto l = some c)
    (hT1 : ThInvE p E1 { th with promises := th.promises ++ [c.mem.size] })
    (hm1 : MemInv (gOf p k arch (promise c j a v w) j) E1
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }))
    (hTy1 : TyOKE (gOf p k arch (promise c j a v w) j) E1) (hRc1 : RecFresh (gOf p k arch (promise c j a v w) j) j th.nalloc)
    (hR1 : TermPtrRts.PtrRtsE sto
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] })
      { th with promises := th.promises ++ [c.mem.size] } l)
    (ht1 : TermPtrRts.tminOf sto
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] })
      l = some c.mem.size)
    (hbf : (promise c j a v w).boxFence = true)
    (hfr : ∀ q, th.nalloc ≤ q → sto (freshLabel (promise c j a v w).lbase (promise c j a v w).n j q) = none)
    (hL : TermPtrRts.ThLbl { pfr := E1.pfr, box := E1.box } { th with promises := th.promises ++ [c.mem.size] })
    (hSC : TermTyped.StoClo E1) (hps : TermScope.ProgScopeOK p = true)
    (hD : TermScope.ThScope { th with promises := th.promises ++ [c.mem.size] })
    (hC : ∀ t', TermPtrRts.tminOf sto (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) l = some t' →
      TermPtrRts.MemRtsC sto t' l (promise c j a v w).mem (promise c j a v w).pairs (th.promises ++ [c.mem.size]))
    (hG : TermPtrRts.GranuleWP sto (promise c j a v w).mem (promise c j a v w).pairs (th.promises ++ [c.mem.size]))
    (hLay : ∀ l cl, sto l = some cl → LayT cl.ty) (hsa : ∃ cl, E1.sto l = some cl) (hpa : E1.pfr l ≠ none)
    (hba : E1.box l = none)
    (hBS : ∀ t', TermPtrRts.tminOf sto (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) l = some t' →
      TermPtrRts.BoxSep E1 t' l (promise c j a v w).mem)
    (hTA1 : TermTyped.TidAt j (promise c j a v w) E1)
    (hNa1 : ∀ th', (promise c j a v w).ths[j]? = some th' → th'.tidLbl ≠ some l) :
    th.vs.vWr ≤ w := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hth1 := hpi.2.1
  have hNo := hNP j l (promise c j a v w) _ E1 sto c.mem.size hk hs1
    (fun c2 hs hc => hCSP X c2 hs hc) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw)
    E0u E1 hwin hAn
    (by obtain ⟨_, η, _, rfl, -⟩ := hT1; exact Ext_refl (Coh_CE η) (CohR_CE η)) hTA1 hNa1 hth1 hT1 hm1 hTy1 hRc1 hR1 ht1 hbf hfr hL hSC hps hD
    hC hG hLay hsa hpa hba hBS
  have h1 : (promise c j a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [hpi.1, Array.getElem?_push]; simp
  have hmB : ∀ c2, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c2 →
      c2.mem[c.mem.size]? = some ⟨a, v, w⟩ := fun c2 hs => W2New.solo_mem hs.toSolo h1
  obtain ⟨cs, hs, hn⟩ := X.cert
  have h2 := TermPtrRts.winLe_gen (j := j) (a := l) (c1 := promise c j a v w) hNo hmB hs hn (.refl _)
    { th with promises := th.promises ++ [c.mem.size] } hth1
    (List.mem_append_right _ (List.mem_singleton.2 rfl))
  exact h2

end

end TermPlantAtI

#print axioms TermPlantAtI.idxBody_keep
#print axioms TermPlantAtI.idxBody_plant
#print axioms TermPlantAtI.cfgCoh_run
#print axioms TermPlantAtI.plant_vWr
#print axioms TermPlantAtI.wordOK_lt
#print axioms TermPlantAtI.priv_le_coh_def
#print axioms TermPlantAtI.priv_le_coh
