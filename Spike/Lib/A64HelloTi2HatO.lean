/-
**`HMidPAH.ti`'s discharger with the level lift under `OffW`** (AArch64): `HelloTi2Hat.hti_H`
with its `hWX` taking the writes off the arena as an antecedent (`H1GAH.hWX`'s shape), fed by the segment itself
(`Ti2OffW.ti2_WSH_off`): the root's former `hoffTi` field (unprovable as stated) is removed. The statement and proof are `hti_H`'s but for
`hWX` and the nodes' obligations; the control's hold is `SpawnSrcH`'s (`MidG`'s source facts).

- `hti_HO`: `HMidPAH.ti` from `hWX` under `OffW`.
-/
import Spike.Lib.A64HelloTi2Hat
import Spike.Lib.A64HelloTi2OffW

namespace Spike.Lib.HelloTi2HatO

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
open Spike.Lib.HelloTi2Hat (site_ne_clonePcH)

set_option maxHeartbeats 3200000 in
/-- **`HMidPAH.ti` from the level lift under `OffW`** (`hti_H`, module doc). -/
theorem hti_HO {L : RuntimeLayout} {W X : FragS isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2}
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
      WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.A64.HelloW2.OffW ar s →
      W s c [] ∧ X s c [])
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
  -- the control's hold (`SpawnSrcH`'s)
  have hh : c0.hold = none := by
    obtain ⟨_, _, ⟨-, -, hS⟩, -⟩ := hM.1
    exact hS.2.1
  -- the nodes inside `WSH ∧ OffW` at `X0TH`, then at `NoMsrAt`
  have hT := Spike.Lib.A64.HelloPh.Ti2OffW.ti2_WSH_off (P := Pz (r1Of L.lab))
    (L := L) (a := a) (rS := r1Of L.lab) (ar := ar) (p := p) (Dt := Dt) (Cl := Cw)
    (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (frM := frM c0)
    (X0 := X0TH L (L.lab siteL))
    hp hlo hlab hsite hcl (hSctl c0 cA hM.1) (hpl c0 sl me cA fr hM) hPlK
    (Spike.Lib.A64.HelloPh.Ti2.x0TH_ti hlab rfl)
    (Spike.Lib.A64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hΛ hs hro hR hal hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (tH L.lab) c0 g) rfl hh hmF (fun a ha m h => hunF a ha m (hFF m h)) hnoF
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
        · exact absurd (hCl s hcl') hw.1.1.2.1.1
      · exact fun hk => .inl hk
  -- `WSH` gives `W ∧ X`
  have hseg2 := hseg1.mono_W (W' := fun s c => (W s c [] ∧ X s c []) ∧ NoMsrAt s)
    fun s c hw => ⟨hWX c0 cA hM.1 s c hw.1.1 hw.1.2, hw.2⟩
  refine hseg2.mono_post fun s c h => ?_
  obtain ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM'⟩, hJ⟩ := h
  exact ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM'⟩


end Spike.Lib.HelloTi2HatO

/-- info: 'Spike.Lib.HelloTi2HatO.hti_HO' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloTi2HatO.hti_HO
