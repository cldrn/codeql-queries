import cpp

from AssignExpr a, int level
where a.getLValue().getType().getPointerIndirectionLevel() = level and level > 2
select a, "Assigment using a pointer indirection level of '"+ level + "'. Possible Three Star Programmer detected."
