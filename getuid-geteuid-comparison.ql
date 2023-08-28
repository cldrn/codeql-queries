import cpp

// Define a class for the `geteuid` function
class GetEuidFunction extends Function {
  GetEuidFunction() {
    this.hasName("geteuid")
  }
}

// Define a class for the `getuid` function
class GetUidFunction extends Function {
  GetUidFunction() {
    this.hasName("getuid")
  }
}

// Define a class for the `getgid` function
class GetGidFunction extends Function {
  GetGidFunction() {
    this.hasName("getgid")
  }
}

// Define a class for the `getegid` function
class GetEgidFunction extends Function {
  GetEgidFunction() {
    this.hasName("getegid")
  }
}

from FunctionCall call, Function target, ComparisonOperation comparison
where 
  (
    (call.getTarget() = target and target instanceof GetEuidFunction) or 
    (call.getTarget() = target and target instanceof GetUidFunction)
  ) and 
  call.getParent() = comparison and 
  not exists(FunctionCall prohibitedCall |
    prohibitedCall.getParent() = comparison and 
    (
      prohibitedCall.getTarget() instanceof GetGidFunction or 
      prohibitedCall.getTarget() instanceof GetEgidFunction
    )
  )
select call, "Call to " + target.getName() + " detected inside a comparison without calls to getgid or getegid."
