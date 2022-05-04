/**
 * @name Server-Side Template Injection in RazorEngine
 * @description User-controlled data may be evaluated, leading to arbitrary code execution.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id csharp/razor-injection
 * @tags security
 */

import csharp
import semmle.code.csharp.frameworks.microsoft.AspNetCore
import semmle.code.csharp.dataflow.TaintTracking
import semmle.code.csharp.dataflow.flowsources.Remote
import DataFlow::PathGraph

class RazorEngineServiceExtensionsClass extends Class {
  RazorEngineServiceExtensionsClass() { this.hasQualifiedName("RazorEngine.Templating.RazorEngineServiceExtensions") }

  Method getRunCompileMethod() {
    result.getDeclaringType() = this and
    result.hasName("RunCompile")
  }

  Method getAddTemplateMethod() {
    result.getDeclaringType() = this and
    result.hasName("AddTemplate")
  }

  Method getCompileMethod() {
    result.getDeclaringType() = this and
    result.hasName("Compile")
  }

  Method getCompileRunnerMethod() {
    result.getDeclaringType() = this and
    result.hasName("CompileRunner")
  }
}

class LoadedTemplateSourceClass extends Class {
  LoadedTemplateSourceClass() { this.hasQualifiedName("RazorEngine.Templating.LoadedTemplateSource") }
}

class RazorEngineClass extends Class {
  RazorEngineClass() { this.hasQualifiedName("RazorEngine.Razor") }

  Method getParseMethod() {
    result.getDeclaringType() = this and
    result.hasName("Parse")
  }

  Method getParseManyMethod() {
    result.getDeclaringType() = this and
    result.hasName("ParseMany")
  }

  Method getCompileMethod() {
    result.getDeclaringType() = this and
    result.hasName("Compile")
  }

  Method getCreateTemplateMethod() {
    result.getDeclaringType() = this and
    result.hasName("CreateTemplate")
  }

  Method getCreateTemplatesMethod() {
    result.getDeclaringType() = this and
    result.hasName("CreateTemplates")
  }

  Method getGetTemplateMethod() {
    result.getDeclaringType() = this and
    result.hasName("GetTemplate")
  }

  Method getGetTemplatesMethod() {
    result.getDeclaringType() = this and
    result.hasName("GetTemplates")
  }

  Method getCreateTemplateTypeMethod() {
    result.getDeclaringType() = this and
    result.hasName("CreateTemplateType")
  }

  Method getCreateTemplateTypesMethod() {
    result.getDeclaringType() = this and
    result.hasName("CreateTemplateTypes")
  }
}

class RazorEngineInjection extends TaintTracking::Configuration {
  RazorEngineInjection() { this = "RazorEngineInjection" }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    succ.asExpr().(ArrayInitializer).getAnElement() = pred.asExpr()
    or
    exists(AssignableDefinition def |
      pred.asExpr() = def.getSource() and
      succ.asExpr() = def.getTargetAccess().(ArrayWrite).getQualifier()
    )
    or
    exists(MethodCall mc |
      mc.getQualifiedDeclaration().getReturnType().getQualifiedName().matches("System.Collections.Generic.IEnumerable%") and
      succ.asExpr() = mc and
      pred.asExpr() = mc.getAnArgument()
    )
  }

  override predicate isSource(DataFlow::Node source) {
    source instanceof RemoteFlowSource
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(RazorEngineClass rec, MethodCall mc |
      (
       mc.getTarget() = rec.getParseMethod() or
       mc.getTarget() = rec.getParseManyMethod() or
       mc.getTarget() = rec.getCompileMethod() or
       mc.getTarget() = rec.getCreateTemplateMethod() or
       mc.getTarget() = rec.getCreateTemplatesMethod() or
       mc.getTarget() = rec.getGetTemplateMethod() or
       mc.getTarget() = rec.getGetTemplatesMethod() or
       mc.getTarget() = rec.getCreateTemplateTypeMethod() or
       mc.getTarget() = rec.getCreateTemplateTypesMethod()
      )
      and
      sink.asExpr() = mc.getArgument(0)
    )
    or
    exists(RazorEngineServiceExtensionsClass rec, MethodCall mc |
      (
       mc.getTarget() = rec.getRunCompileMethod() or
       mc.getTarget() = rec.getCompileMethod() or
       mc.getTarget() = rec.getAddTemplateMethod() or
       mc.getTarget() = rec.getCompileRunnerMethod()
      )
      and
      sink.asExpr() = mc.getArgumentForName("templateSource")
    )
    or
    exists(ObjectCreation oc, LoadedTemplateSourceClass t |
      oc.getTarget().getDeclaringType() = t and
      sink.asExpr() = oc.getArgumentForName("template")
    )
  }
}

from RazorEngineInjection cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink,
  "Server-Side Template Injection in RazorEngine leads to Remote Code Execution"
