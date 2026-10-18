import L6Poly.Basic
import L6Check.Certs.C98f8948c205c615f

/-! Cofactor certificates, batch 29: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_98f8948c205c615f : L6.Poly.checkCert L6.Certs.C98f8948c205c615f = true := by native_decide

end L6.Poly.Checks
