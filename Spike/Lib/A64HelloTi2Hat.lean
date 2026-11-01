/-
**`HMidPAH.ti`'s discharger** (AArch64, `hatA`;
the hello twin of `Spike/Lib/A64WakeTi2Hat.lean`): hello's second
`scc_rt_thread_init` call, from `wc_main` on the second TCB `tH` returning to
`.L22_wc_main.sp6`, is a segment inside the level and its fence
`(W ∧ X) ∧ NoMsrAt` under the take of the second stack or a `clone` refusal
(`TakeCK site r1Of Cl`), at `tpXa (ms []) tp`, its post the stack `r1Of` in
private memory.

`Rt.threadInit_segWA` at `r1Of` (`q.k0 = 16384`), its node obligations
`StartTi.ti2_WSH` (inside `StartWf.WSH` at `X0TH`) lifted to `NoMsrAt`
(`Ti2.tiW_nm`); `WSH` gives `W ∧ X` (`hWX`: the level lift, generic here as
hello's `W`, `X` are); the take `TakeK` is `TakeCK`'s off the clone's pc
(`SegW.mono_K`; `X0TH`'s first conjunct, `hCl`).

The callee's frame on the pool and `r1Of` off it come from `BoxPureH`'s base
(`hbase`: `bandP_boxH`, `hout_boxH`, `hRS_boxH`), main's stack owned at the
site (`owned_r0H`) from the box's frame off `R` (`hF0`, `StackOff`), the
call's frame, the take's frame (`TiW`'s `.call` `CallerCells`, via
`ti2_WSH`'s `hXs`) and the take's cells, `R`'s bounds 8-aligned (`hR8`).
Main's slots `-104` (the box's cell) and `-112` (main's id) are kept by the
callee's frames (`slotPH_keep`), and so are the slice's `-144`, `-128`,
`-120` (`slotSlH_keep`: hello's packet carries the slice's words); the
placement of `c0` at them is `hpl`. Left
as named premises: the second TCB's words (`hmF`, `hunF`, `hnoF`, `hoffT`),
the counters off the arena (`hoffL`, `hoffX`), the source's facts (`hSctl`,
`hpl`), the field and take facts (`hfld`, `htk`), `hF0`, the level lift
(`hWX`), the refusal's pc (`hCl`, `hcl`). The child's stack unowned before
its take comes from the pre's `Pz r1Of` (`x0TH_sitePz`), kept by the callee's
frames (`pz_fstable_ti2H`).

- `site_ne_clonePcH`: the take site is off hello's clone's pc.
- `hti_H`: `HMidPAH.ti`.

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloHatA
import Spike.Lib.A64HelloTi2W
import Spike.Lib.A64WakeTiNoMsr
import Spike.Lib.A64HelloTi2HatG
import Spike.Lib.A64HelloTi2Box
import Spike.Lib.A64HelloTi2Slot
import Spike.Lib.A64HelloTi2SlotSl
import Spike.Lib.A64HelloTi2R0

namespace Spike.Lib.HelloTi2Hat

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.HelloWc (FrMGH wcNIH tH)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH)
open Spike.Lib.A64.Flow.WakeWc (MidG tiQ stOk_tpXa)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.KeepTP (NoMsrAt tpXa)
open Spike.Lib.A64ConsumerA (TakeCK)
open Spike.Lib.A64Consumer (Pz Lbl Lsize)
open Spike.Lib.HelloHMid (SBH)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.HelloPh.Ti2 (X0TH SlotPH SlotSlH)
open Spike.Lib.A64.WakePh (lo)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)

open Spike.Lib.A64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **The take site is off hello's clone's pc**: the site is below
`scc_rt_stack_release`, itself below `.L22_wc_main.sp6`, the clone `100`
past it. -/
theorem site_ne_clonePcH {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab siteL).toBitVec.toNat ≠ clonePcH L := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cvH ".L22_wc_main.sp6" = y := by simp [cvH, hy]
  have e : clonePcH L = y + 100 := by
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = y + 100
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 100).toNat = y + 100
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : decide (cvH "scc_rt_stack_release" ≤ cvH ".L22_wc_main.sp6") = true := by
    unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [decide_eq_true_eq] at hd
  have hs : (L.lab siteL).toBitVec.toNat < cvH "scc_rt_stack_release" := by
    have hd2 : decide (cvH siteL < cvH "scc_rt_stack_release") = true := by
      unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
    rw [hl (by simp)]; exact of_decide_eq_true hd2
  rw [e]; omega

set_option maxHeartbeats 3200000 in
/-- **`HMidPAH.ti` at `R`, `F`, `J1`, `tp`**: from the layout's program
hello's (`hp`, `hlo`, `hlab`, `hsite`, `hΛ`), the words' separation at `a`
(`hs`), `BoxPureH`'s base (`hbase`), and the named premises of the file's
header; `WSH`'s arena `ar`, debts `Dt`, refusal `Cw`, contexts `Ctx`, sizes
`lsize` and main frame `frM c0` free (`hWX` lifts it to `W ∧ X`). -/
theorem hti_H {L : RuntimeLayout} {W X : FragS isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2}
    {p : Prog} {lbl : Lbl} {Cl : State → Prop} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
    {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {tp : UInt64}
    {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame}
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hcl : ∀ s, Cw s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hWX : ∀ c0 cA, MidG (SBH l b ws) c0 cA → ∀ s c,
      WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → W s c [] ∧ X s c [])
    (hs : Spike.Lib.A64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hSctl : ∀ c0 cA, MidG (SBH l b ws) c0 cA → (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c0 [])
    (hpl : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m)
    (hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
      (⟨b, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2bH L a j)
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hbase : R.base.toNat + 80 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -400 ∧ 0 ≤ R.hi)
    (hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0)
    (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) R m)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      Ret0.StOk (ms []) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-144) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
      Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48) (-208) 0) F'
        (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')) :
    ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable (TakeCK (L.lab siteL) (r1Of L.lab) Cl) F' →
      (∀ m, F' m → F m) → R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧ (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => (W s c [] ∧ X s c []) ∧ NoMsrAt s)
          (TakeCK (L.lab siteL) (r1Of L.lab) Cl) p lbl (tpXa (ms []) tp)
          (fun s c => At L.exe L.endPc R' F' (tiN L.lab (tiQ (tH L.lab) c0 g) .e) s c ∧ Pz (r1Of L.lab) s.st.1)
          (fun s c => ∃ x, At L.exe L.endPc R' F' (tiX L.lab (tiQ (tH L.lab) c0 g) x) s c ∧
            StackM (r1Of L.lab) s.st.1) := by
  intro c0 sl me cA fr hM R' F' hR hal hRlo hhi hF hKt hFF hR' hCC g hpre hFm
  subst hR'
  obtain ⟨l', A, ⟨-, rfl, -⟩, hcA⟩ := id hM.1
  have hbd := Spike.Lib.A64.HelloPh.Ti2.bandP_boxH hbase
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub L hsub
  have hout := Spike.Lib.A64.HelloPh.Ti2.hout_boxH (L := L) hbase
  have hRS := Spike.Lib.A64.HelloPh.Ti2.hRS_boxH (L := L) hbase
  have hrc : Spike.Lib.A64.Rt.RtCodeIn0 L.prog := hp ▸ Spike.Lib.A64.HelloPh.hello_rtCodeIn0
  -- the return address `.sp6`, from the caller's node
  have hra : g.ra = (L.lab ".L22_wc_main.sp6").toBitVec := by
    obtain ⟨σC, c, hw, -, -, -, hx, -⟩ := hpre
    exact hx.symm.trans hw.2.2.1
  -- the take's frame and `r1Of`'s stability
  have hSM := Ret0.stackM_stable hfit hout
  have hSMt : FStable ((R.callee (-144) (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
      (StackM (r1Of L.lab)) := by
    refine Ret0.stackM_stable hfit fun a h8 ha ha7 => ?_
    show (a : Int) + 8 ≤ (((R.callee (-144) (-256) 0).callee (-48) (-208) 0).base.toNat : Int) + -208 ∨
      (((R.callee (-144) (-256) 0).callee (-48) (-208) 0).base.toNat : Int) + 0 ≤ a
    have hb' := Region.callee_base (hi' := 0) hR (show (R.callee (-144) (-256) 0).lo ≤ -48 + -208 by omega)
      (by decide) (show (-48 : Int) < (R.callee (-144) (-256) 0).hi by omega)
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hal8 : R.base.toNat % 8 = 0 := by have := L.stacks_al; omega
  -- main's slots at the callee's states, for the placement
  have hPlK0 := Spike.Lib.A64.HelloPh.Ti2.slotPH_keep (L := L) hbase ⟨by omega, hRs.2⟩ hcA rfl fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h
    ⟨mC, σC, hA, hJ.2.2.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.2.1, hk⟩
  -- the slice's slots (`FrWH`'s `-144`, `-128`, `-120`), for the packet's words
  have hPlS := Spike.Lib.A64.HelloPh.Ti2.slotSlH_keep (L := L) (sl := sl) hbase ⟨by omega, hRs.2⟩ fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h
    ⟨mC, σC, hA, hJ.2.2.2.2.1, hJ.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.1, hk⟩
  have hPlK := fun m m' h hd => And.intro (hPlK0 m m' h hd) (hPlS m m' h hd)
  -- the nodes inside `WSH` at `X0TH`, then at `NoMsrAt`
  have hT := Spike.Lib.A64.HelloPh.StartTi.ti2_WSH (P := Pz (r1Of L.lab))
    (L := L) (a := a) (rS := r1Of L.lab) (ar := ar) (p := p) (Dt := Dt) (Cl := Cw)
    (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (frM := frM c0)
    (X0 := X0TH L (L.lab siteL))
    hp hlo hlab hsite hcl (hSctl c0 cA hM.1) (hpl c0 sl me cA fr hM) hPlK
    (Spike.Lib.A64.HelloPh.Ti2.x0TH_ti hlab rfl)
    (Spike.Lib.A64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hΛ hs hro hR hal hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (tH L.lab) c0 g) rfl hmF (fun a ha m h => hunF a ha m (hFF m h)) hnoF
    hra rfl hsub hSM hSMt
    hoffT hoffL hoffX
    (fun s hpc hr hm hz h4 h3 => Spike.Lib.A64.HelloPh.Ti2.x0TH_sitePz (site_ne_clonePcH hlab)
      (P := fun s => Ret0.CallerCells (R.callee (-144) (-256) 0) (-48) (-208) 0 s.st.1 ∧
        ∀ k, ((R.callee (-144) (-256) 0).callee (-48) (-208) 0).Off k →
          (Mem.loadInt s.st.1.dmem (((R.callee (-144) (-256) 0).callee (-48) (-208) 0).addr k) 8).isSome)
      (fun s _ _ hm h4 => Spike.Lib.A64.HelloPh.Ti2.owned_r0H hbase hal8 hR8 hRs (hF0 _ (hFF _ hm)) (hCC _ hm)
        h4.1 h4.2) s hpc hr hm hz ⟨h4, h3⟩)
  have hTn := Spike.Lib.A64.WakePh.Ti2.tiW_nm L.lays rfl hrc.ti hrc.take hT
  -- the fields' and the take's facts under `tpXa`
  have hfld' : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      Ret0.StOk (tpXa (ms []) tp) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2 :=
    fun e he => stOk_tpXa (hfld e he)
  have htk' : ∀ g', Spike.Lib.A64.Rt.TakeOkA (tpXa (ms []) tp) F L.exe L.endPc
      ((R.callee (-144) (-256) 0).callee (-48) (-208) 0) F' (Ret0.tiTake (tiQ (tH L.lab) c0 g) g') :=
    fun g' => Spike.Lib.A64.WakePh.Ti2.takeOkA_tpX (htk c0 _ F' hFF rfl g g')
  have hFt : ∀ m pm, F' m → F' (Ret0.takeMem pm (r1Of L.lab) m) :=
    Ret0.takeMem_of_kstable (a := L.lab siteL) (fun s s' hk hm => hKt s s' (.inl hk) hm) L.exe L.endPc
  -- the segment, at `TakeK` of the site
  have hseg := Spike.Lib.A64.Rt.threadInit_segWA (p := p) (lbl := lbl)
    (ms := tpXa (ms []) tp) (F0 := F) L.lays rfl hrc.ti hrc.tiSp hrc.take hF hR hal hRlo hhi hFF
    (tiQ (tH L.lab) c0 g)
    (by show (16384#64 : BitVec 64).toNat + 16384 ≤ 536870912; decide) hfld' htk'
    (P := Pz (r1Of L.lab)) (Spike.Lib.A64.HelloPh.Ti2.pz_fstable_ti2H hbase)
    hTn hRS hfit hout hFt
  -- off the clone's pc `TakeK` of the site is `TakeCK`
  have hseg1 := hseg.mono_K (K' := TakeCK (L.lab siteL) (r1Of L.lab) Cl)
    fun s c hw s' => by
      constructor
      · rintro (hk | ⟨hcl', -⟩)
        · exact hk
        · exact absurd (hCl s hcl') hw.1.2.1.1
      · exact fun hk => .inl hk
  -- `WSH` gives `W ∧ X`
  have hseg2 := hseg1.mono_W (W' := fun s c => (W s c [] ∧ X s c []) ∧ NoMsrAt s)
    fun s c hw => ⟨hWX c0 cA hM.1 s c hw.1, hw.2⟩
  refine hseg2.mono_post fun s c h => ?_
  obtain ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM'⟩, hJ⟩ := h
  exact ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM'⟩

/-- **`hpl`'s slice antecedent is discharged at the call's frame** (`hti_H`'s `hPlK`): wherever the callee's frame
keeps the cells of a `wcNIH` call state (its `FrWH` spills the slice `sl` at `-144`, `-128`, `-120`), the slots
read `sl`'s `x0`, `x2`, `x3`; no premise beyond `hti_H`'s own (`hbase`, `hRs`, `hFm`'s shape). -/
example {L : RuntimeLayout} {R : Region} {c0 : Ctl} {t me cA : BitVec 64}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {fr : BitVec 64 × BitVec 64} {F' : MachineData → Prop}
    (hbase : R.base.toNat + 80 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -400 ∧ 0 ≤ R.hi)
    (hFm : ∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧ (wcNIH L.lab c0 t sl me cA fr).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → DFrame (R.callee (-144) (-256) 0) m m' →
      SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat m' :=
  Spike.Lib.A64.HelloPh.Ti2.slotSlH_keep (L := L) hbase ⟨by omega, hRs.2⟩ fun m' h =>
    let ⟨mC, σC, _, hA, hJ, hk⟩ := hFm m' h
    ⟨mC, σC, hA, hJ.2.2.2.2.1, hJ.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.1, hk⟩

end Spike.Lib.HelloTi2Hat

/-- info: 'Spike.Lib.HelloTi2Hat.site_ne_clonePcH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTi2Hat.site_ne_clonePcH

/-- info: 'Spike.Lib.HelloTi2Hat.hti_H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTi2Hat.hti_H
