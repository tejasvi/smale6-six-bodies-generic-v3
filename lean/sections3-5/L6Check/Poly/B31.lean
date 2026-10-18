import L6Poly.Basic
import L6Check.Certs.Cb5caef048fd37a47

/-! Cofactor certificates, batch 31: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_b5caef048fd37a47 : L6.Poly.checkCert L6.Certs.Cb5caef048fd37a47 = true := by native_decide

end L6.Poly.Checks
