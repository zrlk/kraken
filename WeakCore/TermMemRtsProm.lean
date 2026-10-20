import WeakCore.TermPtrKey
import WeakCore.TermK2aLabsV
import WeakCore.TermCellOwn

/-!
# TermMemRtsProm: `MemRtsCG` across a promise (K1a, for)

* `noCnt_unpl`: no message that is not an outstanding promise of `j` names, at a counted slot of a cell
  of Σ, an unpublished, box-free cell of `j` (`MemOKP` of a thread whose cut holds the carrier,
  `cntOK_typed`/`cntPairOK_typed`, `labsV_cnt`; `FgnPromCntG` for foreign promises).
* `memRtsCG_prom`: `MemRtsCG` across a promise of `j` at the plant map `P`, for holdings with no own
  key gained; `memRtsCG_promX` at a `PCtx`.
-/

namespace TermMemRtsProm
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermCut TermSys TermMain TermPtrRts TermPtrStab
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem wc_of_shape {S : Ty} {b : Nat} {T : Ty} {ws : List Word} (hseg : SegOf T b S) (hsh : ShapeC S ws) :
    wc S = some ws.length := by
  obtain ⟨L, hL⟩ := TermCntLoc.segOf_accs hseg
  simp only [wc, hL, Option.map_some]
  rw [hsh L hL]

/-- **No counted reference to an unplanted cell**: a message that is not an outstanding promise of
`j`, at a counted slot (single word, or a pair store's second half) of a cell of Σ, names no
unpublished, box-free cell of `j`. -/
theorem noCnt_unpl {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (X : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hFC : FgnPromCntG Eg c)
    {j : Nat} {th : TTh} (hth : c.ths[j]? = some th) {L : AllocLabel} {clL : Cell}
    (hsL : Eg.sto L = some clL) (hoL : clL.owner = some j) (hpL : Eg.pfr L = none) (hbL : Eg.box L = none)
    {u : Ts} {m : Msg} {cl : Cell} (hmu : c.mem[u]? = some m) (hu : u ∉ th.promises)
    (hc : Eg.sto m.loc.label = some cl) (hN : Names L (mw m))
    (hcnt : (NotSnd cl.ty m.loc.offset ∧ CntOK cl.ty m.loc.offset (mw m)) ∨
      ∃ v m0, v + 1 = u ∧ v ∈ c.pairs ∧ c.mem[v]? = some m0 ∧ m0.loc.label = m.loc.label ∧
        CntPairOK cl.ty m0.loc.offset (mw m0) (mw m)) : False := by
  obtain ⟨a', g, hv, hl⟩ := hN
  have hv' : m.val = .loc a' g := hv
  have hlive := X.cellOwn m.loc.label cl hc (Or.inl ⟨u, m, hmu, rfl⟩)
  obtain ⟨i, thi, hthi, hin⟩ : ∃ i thi, c.ths[i]? = some thi ∧ (cl.owner = some i ∨ Eg.Shared m.loc.label) := by
    cases ho : cl.owner with
    | some i =>
      have hi := hlive.1 i ho
      exact ⟨i, c.ths[i], Array.getElem?_eq_getElem hi, Or.inl rfl⟩
    | none => exact ⟨j, th, hth, Or.inr (hlive.2 ho)⟩
  have hQ : ∀ (S : AllocLabel → Prop) (vw : Ts), ¬ TermK2aLabsV.QV (CE (Cut Eg i S).unsee) L vw := by
    intro S vw hq
    rcases hq with ⟨f, hf, -⟩ | ⟨B, hB⟩
    · have hf0 : Eg.pfr L = some f := hf
      rw [hpL] at hf0; cases hf0
    · have hB0 : Eg.box L = some B := hB
      rw [hbL] at hB0; cases hB0
  rcases hcnt with ⟨hU, hC⟩ | ⟨v0, m0, hv1, hvp, hm0, hl0, hC⟩
  · by_cases hpi : u ∈ thi.promises
    · rcases hFC i thi u m hthi hpi hmu a' g hv' cl hc hU hC with ⟨f, hf⟩ | ⟨cl2, hs2, ho2⟩ | ⟨B, hB⟩ |
        ⟨n0, -, hs0⟩
      · rw [hl, hpL] at hf; cases hf
      · rw [hl, hsL] at hs2
        cases hs2
        rw [hoL] at ho2
        cases ho2
        rw [hth] at hthi
        cases hthi
        exact hu hpi
      · rw [hl, hbL] at hB; cases hB
      · rw [hl, hsL] at hs0; cases hs0
    · obtain ⟨S, -, -, hm, -⟩ := X.thr i thi hthi
      have hcc : (Cut Eg i S).sto m.loc.label = some cl := by
        rw [Cut_sto]; exact cutSto_some.2 ⟨hc, hin⟩
      rcases hm.1.1 u m cl hpi hmu hcc with hun | hW
      · rw [hun] at hv'; cases hv'
      · obtain ⟨b, S0, ws, oo, w0, hseg, ⟨⟨hvr, hval⟩, hsh⟩, hw0, hle, -, hcI⟩ := TermCntLoc.cntOK_typed hC hW hU
        have hq := TermK2aLabsV.labsV_cnt (η := CE (Cut Eg i S).unsee) (fun _ _ _ h => h) rfl
          (wc_of_shape hseg hsh) hval hvr oo hcI w0 a' g hw0 (hle.1.trans hv')
        rw [hl] at hq
        exact hQ S _ hq
  · obtain ⟨S, -, -, hm, -⟩ := X.thr i thi hthi
    have hc0 : (Cut Eg i S).sto m0.loc.label = some cl := by
      rw [Cut_sto, hl0]; exact cutSto_some.2 ⟨hc, hin⟩
    have hmu' : c.mem[v0 + 1]? = some m := by rw [hv1]; exact hmu
    have hW := hm.1.2.1 v0 m0 m cl hvp hm0 hmu' hc0
    obtain ⟨b, S0, ws, oo, x0, x1, hseg, ⟨⟨hvr, hval⟩, hsh⟩, -, hx1, -, hle1, -, hcI⟩ :=
      TermCntLoc.cntPairOK_typed hC hW
    have hq := TermK2aLabsV.labsV_cnt (η := CE (Cut Eg i S).unsee) (fun _ _ _ h => h) rfl
      (wc_of_shape hseg hsh) hval hvr (oo + 1) hcI x1 a' g hx1 (hle1.1.trans hv')
    rw [hl] at hq
    exact hQ S _ hq

theorem lt_push {mem : Memory} {x : Msg} {u : Ts} {m : Msg} (h : (mem.push x)[u]? = some m) :
    u < mem.size + 1 := by
  have h1 := Promises.lt_size_of_getElem? h
  rw [Array.size_push] at h1
  exact h1

/-- The counted-slot premise of `MemRtsC` at the pushed memory, off the new message, is the one at the
old memory. -/
theorem cnt_unpush {mem : Memory} {pairs : List Ts} {x : Msg} {u : Ts} {m : Msg} {T : Ty}
    (hu : u < mem.size)
    (h : (NotSnd T m.loc.offset ∧ CntOK T m.loc.offset (mw m)) ∨
      ∃ v m0, v + 1 = u ∧ v ∈ pairs ∧ (mem.push x)[v]? = some m0 ∧ m0.loc.label = m.loc.label ∧
        CntPairOK T m0.loc.offset (mw m0) (mw m)) :
    (NotSnd T m.loc.offset ∧ CntOK T m.loc.offset (mw m)) ∨
      ∃ v m0, v + 1 = u ∧ v ∈ pairs ∧ mem[v]? = some m0 ∧ m0.loc.label = m.loc.label ∧
        CntPairOK T m0.loc.offset (mw m0) (mw m) := by
  rcases h with h | ⟨v, m0, hv1, hvp, hm0, hl, hC⟩
  · exact Or.inl h
  · have hvn : v ≠ mem.size := by
      intro e
      rw [e] at hv1
      rw [← hv1] at hu
      exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt hu)
    exact Or.inr ⟨v, m0, hv1, hvp, push_get_ne hm0 hvn, hl, hC⟩

/-- **`MemRtsCG` across a promise of `j`** at the plant map `P` (`hPL`), for holdings `HP2` with no
own key gained (`hkey`), from `SysInvN`, `PtrRtsGL` before and `FgnPromCntG`. -/
theorem memRtsCG_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP HP2 : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {N : AllocLabel → Nat} {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val}
    {w : Ts}
    (X : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[j]? = some th)
    (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0)
    (hG : PtrRtsGL Eg Tot HP c) (hkey : ∀ q l, (Tot q + HP2 q) (.own l) ≤ (Tot q + HP q) (.own l))
    (hFC : FgnPromCntG Eg c) :
    MemRtsCG (EgP Eg P N j n) Tot HP2 (promise c j a v w) := by
  have hNE := noEdgeUnpl_of X.promClos X.promInCut
  have hplt := X.plt
  have hi := promise_inv (a := a) (v := v) (w := w) hth
  have hpairs : (promise c j a v w).pairs = c.pairs := by rw [hi.1]
  intro q thq L cl f hq hsto hown hpf hk t ht
  have hsto0 : Eg.sto L = some cl := hsto
  have hk0 : 0 < (Tot q + HP q) (.own L) := Nat.lt_of_lt_of_le hk (hkey q L)
  show MemRtsC Eg.sto t L (promise c j a v w).mem (promise c j a v w).pairs thq.promises
  rw [promise_mem hth, hpairs]
  by_cases hqj : q = j
  · rw [hqj] at hq hown hk0 ht
    rw [hi.2.1] at hq
    cases hq
    cases hP : P L with
    | none =>
      have hpf0 : Eg.pfr L = some f := by rw [egP_pfr_none hP] at hpf; exact hpf
      obtain ⟨t0, ht0⟩ := Option.ne_none_iff_exists'.1 (hG.2.2.1 j L cl f hsto0 hown hpf0 hk0)
      rw [tminG_prom_own_some (a := a) (v := v) (w := w) hth hplt ht0] at ht
      have e0 := Option.some.inj ht
      subst e0
      have hM := hG.2.2.2 j th L cl f hth hsto0 hown hpf0 hk0 t0 ht0
      intro u m cl' hu hnp hc hN hcnt
      have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
      have hlt : u < c.mem.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (lt_push hu)) hne
      exact hM u m cl' (push_get_ne hu hne) (fun h => hnp (List.mem_append_left _ h)) hc hN
        (cnt_unpush hlt hcnt)
    | some f' =>
      obtain ⟨cl2, hcl2, -, hpn0⟩ := plantOf_target hPL hP
      rw [hsto0] at hcl2
      cases hcl2
      rw [tminG_plant hNE hth hPL hplt hsto0 hown hpn0 hP] at ht
      cases ht
      have hbox := box_none_of_sto X.boxSto hsto0
      intro u m cl' hu hnp hc hN hcnt
      exfalso
      have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
      have hlt : u < c.mem.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (lt_push hu)) hne
      exact noCnt_unpl X hFC hth hsto0 hown hpn0 hbox (push_get_ne hu hne)
        (fun h => hnp (List.mem_append_left _ h)) hc hN (cnt_unpush hlt hcnt)
  · rw [promise_other hqj] at hq
    rw [tminG_prom_fgn hth hplt hqj] at ht
    have hpf0 : Eg.pfr L = some f := by
      cases hP : P L with
      | none => rw [egP_pfr_none hP] at hpf; exact hpf
      | some f' =>
        obtain ⟨cl', hcl', ho', -⟩ := plantOf_target hPL hP
        rw [hsto0] at hcl'
        cases hcl'
        rw [hown] at ho'
        cases ho'
        exact absurd rfl hqj
    have hM := hG.2.2.2 q thq L cl f hq hsto0 hown hpf0 hk0 t ht
    intro u m cl' hu hnp hc hN hcnt
    by_cases hun : u = c.mem.size
    · rw [hun]
      rw [tminG_eq hq] at ht
      exact Nat.le_of_lt (hplt q thq t hq (tminOf_spec ht).1)
    · have hlt : u < c.mem.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (lt_push hu)) hun
      exact hM u m cl' (push_get_ne hu hun) hnp hc hN (cnt_unpush hlt hcnt)

/-- **`MemRtsCG` across the promise of a `PCtx`** (holdings `upd HP j HP'`, `TermPtrKey.ownKey_prom_le`). -/
theorem memRtsCG_promX {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res} {N : AllocLabel → Nat} {n : Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (hG : PtrRtsGL Eg Tot HP c) (hFC : FgnPromCntG Eg c) :
    MemRtsCG (EgP Eg P N j n) Tot (upd HP j HP') (promise c j a v w) :=
  memRtsCG_prom X.inv X.hth hPL hG (TermPtrKey.ownKey_prom_le X hA hdb) hFC

end

end TermMemRtsProm

#print axioms TermMemRtsProm.noCnt_unpl
#print axioms TermMemRtsProm.memRtsCG_prom
#print axioms TermMemRtsProm.memRtsCG_promX
