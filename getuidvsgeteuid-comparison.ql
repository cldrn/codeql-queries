import cpp

from FunctionCall fcall, Assignment a, Variable v, EqualsExpr eq
where 
  (
    (
      fcall.getTarget().hasName("getuid") and
      a.getRValue() = fCall and
      a.getLValue() = v.getAnAccess()
    ) or (
      fcall.getTarget().hasName("geteuid") and
      a.getRValue() = fCall and
      a.getLValue() = v.getAnAccess()
    )
  ) and (
    (
      eq.getLeftOperand().(VariableAccess).getTarget() = v and
      eq.getRightOperand().(VariableAccess).getTarget().getName() = "getuid"
    ) or (
      eq.getLeftOperand().(VariableAccess).getTarget() = v and
      eq.getRightOperand().(VariableAccess).getTarget().getName() = "getuid"
    )
  )
select eq, "Detected comparison of getuid() and geteuid() results."
