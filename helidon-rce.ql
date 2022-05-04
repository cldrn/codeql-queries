import java
import semmle.code.java.dataflow.FlowSources

class UrlConfigSourceHelidon extends RefType {
    UrlConfigSourceHelidon() {
      this.hasQualifiedName("io.helidon.config", "UrlConfigSource")
    }
  }
  
  class HelidonConfigGenericContent extends MethodAccess {
    HelidonConfigGenericContent() {
      exists(Method m | m.getDeclaringType() instanceof UrlConfigSourceHelidon and
        m.hasName("genericContent") and
        m = this.getMethod()
      )
    }
  }


  /**
 * A taint-tracking configuration for tracking untrusted user input used in log entries.
 */
private class HelidonConfiguration extends TaintTracking::Configuration {
    HelidonConfiguration() { this = "Helidon YAML Injection" }
  
    override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }
  
    override predicate isSink(DataFlow::Node sink) {
      sink.asExpr() = any(HelidonConfigGenericContent c)
    }
  
    override predicate isSanitizer(DataFlow::Node node) {
      node.getType() instanceof BoxedType or node.getType() instanceof PrimitiveType
    }
  }

from HelidonConfiguration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "$@ flows to call.", source.getNode(),
  "User-provided value"
