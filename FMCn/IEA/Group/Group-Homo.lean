import FMCn.IEA.Group.Definitions
import FMCn.IEA.Group.TheoremsM
import FMCn.IEA.Group.TheoremsA

open MonoidM MonoidA

theorem Criterion_Resp_OpM [GroupM G] [GroupM H] (φ : G → H) :
  φ resp(⋆) → φ G-Mhomo :=
by
  intro hop
  have hid : φ resp'e' := by
    have h' : (φ e) ⋆ (φ e) = (φ e) := by
      rw [← hop, opm_id]
    exact Opm_Only_Id (φ e) (e : H) ⟨(Idempot_means_idm (φ e) h'), ⟨opm_id, id_opm⟩⟩
  refine ⟨hop, hid, ?_⟩
  · intro a
    suffices h' : (φ a⁻¹) is_(⋆)-invOf (φ a) from Cheap_Invm_R (φ a) (φ a⁻¹) h'.2
    refine ⟨?_, ?_⟩
    · rw [← hop, GroupM.minv_opm, hid]
    · rw [← hop, GroupM.opm_minv, hid]

--------------------------------------------------------------

theorem Criterion_Resp_OpA [GroupA G] [GroupA H] (φ : G → H) :
  φ resp(⊹) → φ G-Ahomo :=
by
  intro hop
  have hid : φ resp'z' := by
    have h' : (φ z) ⊹ (φ z) = (φ z) := by
      rw [← hop, opa_id]
    exact Opa_Only_Id (φ z) (z : H) ⟨(Idempot_means_ida (φ z) h'), ⟨opa_id, id_opa⟩⟩
  refine ⟨hop, hid, ?_⟩
  · intro a
    suffices h' : (φ (−a)) is_(⊹)-invOf (φ a) from Cheap_Inva_R (φ a) (φ (−a)) h'.2
    refine ⟨?_, ?_⟩
    · rw [← hop, GroupA.ainv_opa, hid]
    · rw [← hop, GroupA.opa_ainv, hid]
