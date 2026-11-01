/-
**hello.w's `hmid` with `scc_rt_thread_init`'s take** (AArch64,
`hatA`; the hello twin of
`Spike/Lib/A64WakeHatA.lean`): `HelloHMid.hmid_boxH` with the callee's
segment inside the level and its fence `W ∧ X ∧ NoMsrAt` under the take of
the second stack or a `clone` refusal (`TakeCK site r1Of Cl`), the late
frame condition `F ∧ StackM r1Of` (the child's stack private at the clone),
rather than inside `NoMsrW (WBH L W)` at no outside move (where the take
site is excluded, so `HMidPH.ti` admits no take).

`hello_wc_mid_hatK` from the landing: `WBH`'s nodes (`WcMidWH.antiF₂`,
`WcMidWH.noMsr`) are in `W ∧ X` (`hX`, wake's `x1W_off`), unmoved by
`TakeCK`; `TakeCK` keeps `F` (`takeCK_fK`, from `HMidPAH.fcl`, `fcg`), `R`'s
cells (`takeCKH_kR`, `R.hi ≤ 80`) and the thread pointer (`takeCK_tp`);
`TakeCK` is `TakeCKS` at the fence's states (`hXr`: the site's range is
`r1Of` at the take site; wake's `k1W_iff`).

- `HMidPAH`: `HMidPH` with the ghost facts wake's `BoxPure` has beyond
  `BoxPureH` (`hi80`, `fcl`, `fcg`), `ti` at the callee's take
  (`HelloPh.Ti2.hti_H`'s conclusion), `wcl` as `HMidPH.wcl`
  (wake's `HMidPA`);
- `takeCK_iffH`: `TakeCKS site Cl` is `TakeCK site r1Of Cl` where the
  site's range is `r1Of` at the site (wake's `k1W_iff`);
- `hmid_boxAH`: the segment from `BoxMH` with `r1Of` unmapped
  (`KeepUn.U`) to `CloneMidH` (wake's `hmid_boxA`).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloHMid
import Spike.Lib.A64HelloWcHatK

namespace Spike.Lib.HelloHatA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.HelloWc (WcMainWH bXH FrMGH rNH ResCtxH TcbCtxH wcNCH tcb2QH tH rARH wcNIH
  hello_wc_mid_hatK wcMidW_offCH wcMidW_w1H takeCKH_kR stackM_r1H)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH wcNSH)
open Spike.Lib.A64.Flow.WakeWc (MidG kOf tiQ pcOf_ne takeCK_fK takeCK_tp)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX CallerCells StackM TakeK)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)
open Spike.Lib.A64ConsumerA (TakeCK TakeCKS)
open Spike.Lib.A64Consumer (Pz)
open Spike.Lib.HelloHMid (BoxPureH BoxMH QBH SBH WBH CloneMidH at_bXH_ms)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH src_spawnH)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Sem.A64 (pcOf)

/-- **`hmid`'s named premises at one ghost with the callee's take** (`R`,
`F`, `J1`, `tp`) inside the level `W` and its fence's extra `X` under the
memory side `ms` at no frames, for the source `p`, the placement `lbl`, the
box's label `l` at `b`, the clone's refusal `Cl`; `Wc` the level's extra
fact at the clone: `HMidPH`'s `wcWf`, `res`, `tcb`, `resA`, `hdrA`, `tcbA`,
`tid`, `wcl`; `R` ending below the second stack and `F` kept by its take
(`hi80`, `fcl`, `fcg`: wake's `BoxPure`'s); the callee at the take (`ti`). -/
structure HMidPAH (L : RuntimeLayout) (W X : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (Cl : State → Prop) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (R : Region)
    (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (tp : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W` (`HMidPH.wcWf`). -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- The reserve's nodes inside `W` (`HMidPH.res`). -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W` (`HMidPH.tcb`). -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `hello_wc_mid_hatK`'s `hres` (`HMidPH.resA`). -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `hello_wc_mid_hatK`'s `hhdr` (`HMidPH.hdrA`). -/
  hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `hello_wc_mid_hatK`'s `htcb` (`HMidPH.tcbA`). -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0)
  /-- `hello_wc_mid_hatK`'s `htid` (`HMidPH.tid`). -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `R` ends below the second stack (wake's `BoxPure`'s `R.hi ≤ 48`, at
  `wc_main`'s base 80 below it: `takeCKH_kR`, `stackM_r1H`). -/
  hi80 : R.hi ≤ 80
  /-- `F` closed under the take of `r1Of` (wake's `BoxPure`'s; `takeCK_fK`). -/
  fcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m)
  /-- `F` determined by the memory (wake's `BoxPure`'s; `takeCK_fK`). -/
  fcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m'
  /-- The callee inside `W ∧ X ∧ NoMsrAt` at the take of `r1Of` or a
  refusal (`hello_wc_mid_hatK`'s `hti`; `HelloPh.Ti2.hti_H`'s
  conclusion; wake's `HMidPA.ti`). -/
  ti : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) F' →
      (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧ (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => (W s c [] ∧ X s c []) ∧ NoMsrAt s)
          (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) p lbl (tpXa (ms []) tp)
          (fun s c => At L.exe L.endPc R' F' (tiN L.lab (tiQ (tH L.lab) c0 g) .e) s c ∧ Pz (r1Of L.lab) s.st.1)
          (fun s c => ∃ x, At L.exe L.endPc R' F' (tiX L.lab (tiQ (tH L.lab) c0 g) x) s c ∧
            StackM (r1Of L.lab) s.st.1)
  /-- `W` and its extra `Wc` at the clone's `svc` (`HMidPH.wcl`), the child's
  stack private there (the hat's late frame condition `F ∧ StackM r1Of`; the
  instance's `Wc := StackM r1Of`). -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c

/-- **`TakeCKS` is the callee's move** where the site's range is `rS` at
the take's pc `a` (wake's `k1W_iff`). -/
theorem takeCK_iffH {a : Int64} {rS : Scc.Sem.Range} {Cl : State → Prop} {s : State}
    (hr : s.st.2 = a → Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = rS) (s' : State) :
    TakeCKS a Cl s s' ↔ TakeCK a rS Cl s s' := by
  by_cases ha : s.st.2 = a
  · show TakeK _ (Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s) s s' ∨ _ ↔ TakeK _ _ s s' ∨ _
    rw [hr ha]
  · exact ⟨fun h => h.imp (fun h => (ha h.1).elim) id, fun h => h.imp (fun h => (ha h.1).elim) id⟩

set_option maxHeartbeats 800000 in
/-- **`hmid` at `l`, `b`, `n` with the callee's take**: from the box's
landing `BoxMH` (under `ms0`) with the second stack unmapped (`U r1Of`) past
its store to main's clone (`CloneMidH`) inside the level `W` and the fence's
extra `X`, under the take of the site's range or a refusal `Cl` at the
clone (`TakeCKS`): `hmid_boxH`'s premises, the site's range `r1Of` at the
take site in the fence (`hXr`; wake's `X1W`'s take clause), the second
stack in the address space (`hfit1`; wake's from A13's data part), and
`HMidPAH` at every ghost of `BoxMH`'s (`hP`). -/
theorem hmid_boxAH {L : RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop} {W X : FragS isaLSE2}
    {Wc : Frag isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {Cl : State → Prop} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} (hp : L.prog = SccCode.helloProg) (hK : (ms []).K = some Scc.Sem.A64.abi) (hpub : (ms []).pub)
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hX : ∀ s c, pcOf s ≠ clonePcH L → pcOf s ≠ (L.lab Ret0.StackTake.siteL).toBitVec.toNat → X s c [])
    (hXr : ∀ s c, W s c [] → X s c [] → s.st.2 = L.lab Ret0.StackTake.siteL →
      Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = r1Of L.lab)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64)
    (hokb : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 L.lab → q.OKB (ms []) L.lab)
    (hg : (ms []).heap = ms0.heap ∧ (ms []).cells = ms0.cells ∧ (ms []).off = ms0.off ∧
      (ms []).units = ms0.units)
    (hP : ∀ R F J1 t, BoxPureH L F0 n R F J1 t → G R F J1 t → HMidPAH L W X Wc ms p lbl Cl l b ws R F J1 t) :
    SegWS (fun s c fs => W s c fs ∧ X s c fs) (TakeCKS (L.lab Ret0.StackTake.siteL) Cl) p lbl ms
      (fun s c fs => BoxMH L ms0 F0 G l b ws n s c ∧ A64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L F0 G W Wc l b ws n) := by
  have hpS : Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPureH L F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ G g.1 g.2.1 g.2.2.1 g.2.2.2 ∧
      (At L.exe L.endPc g.1 g.2.1 (bXH ms0 L.lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QBH l b ws l b c ∧
      A64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
    fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J1, t⟩ := g
    by_cases hC : BoxPureH L F0 n R F J1 t ∧ G R F J1 t
    case neg =>
      exact ⟨fun _ _ _ => False, fun _ _ _ h => hC ⟨h.1, h.2.1⟩, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨hB, hG⟩ := hC
    have hp' := hP R F J1 t hB hG
    obtain ⟨hR, hal, hF, hlo, hhi, hst, -, -, -⟩ := id hB
    have hfence : Spike.Lib.A64.Flow.HelloWc.WcMidWH (NoMsrW (WBH L W) (fun _ _ => False)) (fun _ _ => False)
        L.exe L.endPc R F (fun m => F m ∧ StackM (r1Of L.lab) m) (tpXa (ms []) t) J1 (SBH l b ws) (QBH l b ws) :=
      Spike.Lib.A64.Flow.HelloWc.WcMidWH.noMsr hpS hendS
        (Spike.Lib.A64.Flow.HelloWc.WcMidWH.antiF₂ (fun _ h => h.1)
          (Spike.Lib.A64.Flow.HelloWc.WcMidWH.mapWK
            (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk => ⟨⟨hw, pcOf_ne hc, pcOf_ne ha⟩, hk⟩)
            (Spike.Lib.A64.Flow.HelloWc.WcMidWH.and (wcMidW_offCH hpS) (wcMidW_w1H W hp'.wcWf hp'.res hp'.tcb))))
    have hW : Spike.Lib.A64.Flow.HelloWc.WcMidWH (fun s c => (W s c [] ∧ X s c []) ∧ NoMsrAt s)
        (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) L.exe L.endPc R F
        (fun m => F m ∧ StackM (r1Of L.lab) m) (tpXa (ms []) t) J1 (SBH l b ws) (QBH l b ws) :=
      Spike.Lib.A64.Flow.HelloWc.WcMidWH.mapWK (fun s c ⟨⟨hw, hc, ha⟩, hnm, _⟩ _ =>
        ⟨⟨⟨hw, hX s c hc ha⟩, hnm⟩,
          fun s' hk => hk.elim (fun h => ha (by unfold pcOf; rw [h.1])) fun h => hc (hCl s h.1)⟩) hfence
    have hseg := hello_wc_mid_hatK (p := p) (lbl := lbl) (ms := ms []) (tp := t)
      (W := fun s c => W s c [] ∧ X s c []) (K := TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl)
      (M := StackM (r1Of L.lab)) (F₂ := fun m => F m ∧ StackM (r1Of L.lab) m)
      hK hpS hendS hF hR hal hlo hhi
      (fun m m' h hd => ⟨hF m m' h.1 hd, stackM_r1H hp'.hi80 hst hfit1 m m' h.2 hd⟩)
      (fun _ h1 h2 => ⟨h1, h2⟩) hW
      (fun _ _ _ ⟨e1, e2, ht, hh, ho, hme, hsl⟩ =>
        (src_spawnH hpub ht hh ho hme hsl).imp fun _ h => ⟨h.1, e1, e2, h.2⟩)
      hp'.resA hp'.hdrA hp'.tcbA hp'.tid (takeCK_fK hp'.fcl hp'.fcg)
      (fun s s' hk _ k hk' _ => takeCKH_kR hR hp'.hi80 hst hfit1 s s' hk k hk') takeCK_tp
      (fun s _ _ ⟨ho1, ho2⟩ _ hk => hk.elim (fun h => (ho2 h.1).elim)
        fun h => (pcOf_ne ho1 (hCl s h.1)).elim) hp'.ti
    have hseg := hseg.mono_K (K' := TakeCKS (L.lab Ret0.StackTake.siteL) Cl) fun s c ⟨hw, hx⟩ s' =>
      takeCK_iffH (hXr s c hw hx) s'
    refine ((SegWS.liftS [] hseg fun s c h => h).mono_pre ?_).mono_post ?_
    · rintro s c fs ⟨-, -, ⟨hA, htp⟩, hq, hu, rfl⟩
      exact ⟨⟨⟨l, b, at_bXH_ms hokb hg hA, hq⟩, hu, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨sl, me, cA, fr, ⟨l', A, ⟨e1, e2, hsrc⟩, hcA⟩, hFr, hA, hb, htp⟩, rfl⟩
      subst e1 e2
      have hAF : At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c :=
        let ⟨he, hn', hd, hpc, σ, hAb, hD, hJ'⟩ := hA; ⟨he, hn', hd, hpc, σ, hAb, hD.1, hJ'⟩
      have hSM : StackM (r1Of L.lab) s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA; hD.2
      have hw := hp'.wcl s c sl me cA fr hAF hsrc hcA hFr hSM
      exact ⟨rfl, hw.1, hw.2, R, F, J1, t, sl, me, cA, fr, hB, hG,
        hFr, hcA, hsrc, hAF, hb, htp⟩
  · rintro s c fs ⟨⟨R, F, J1, t, hB, hG, hAt, hq⟩, hu, rfl⟩
    exact ⟨(R, F, J1, t), hB, hG, hAt, hq, hu, rfl⟩

end Spike.Lib.HelloHatA

/-- info: 'Spike.Lib.HelloHatA.takeCK_iffH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHatA.takeCK_iffH

/-- info: 'Spike.Lib.HelloHatA.hmid_boxAH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHatA.hmid_boxAH
