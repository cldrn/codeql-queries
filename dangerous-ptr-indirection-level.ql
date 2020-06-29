import cpp

from AssignExpr a, int level
where a.getLValue().getType().getPointerIndirectionLevel() = level and level > 3
select a, "Assigment using a pointer indirection level of '"+ level + "'. This could be over-complicated and prone to errors"
