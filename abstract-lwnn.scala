import scala.io._
import scala.util._
import scala.math._
import scala.collection.mutable.{ HashMap ⇒ HMap }
import pllab.lwnn.syntax._
import Pretty.{ stmt2str ⇒ pretty }
import pllab.lwnn.abstract_domains._

// main interpreter entry point
object ALwnn {

  // the integer abstraction function (chosen by the command-line
  // argument given to the abstract interpreter)
  var α = Z.α _

  def main(args: Array[String]) {
    val ast = ParseL.getAST(Source.fromFile(args(0)).mkString)

    // determine which abstract integer domain to use
    args(1) match {
      case "--const" ⇒ α = Z.α _
      case _ ⇒ sys.error("undefined")
    }

    // worklist with initial state
    var work = Set(State(StmtT(ast), Env(), Store(), haltK))

    // remember set (organized by Label)
    val memo = HMap[Int, State]()

    // calculate fixpoint
    while (!work.isEmpty) {
      work = work.flatMap(_.next).flatMap(
        (ς) ⇒ if (!ς.memo) // this isn't a program point (p.p.)
          Some(ς)
        else if (!(memo contains ς.lbl)) { // first time at this p.p.
          memo(ς.lbl) = ς
          Some(ς)
        } else if (memo(ς.lbl) == memo(ς.lbl) ▽ ς) // nothing new
          None
        else { // new information
          memo(ς.lbl) = memo(ς.lbl) ▽ ς
          Some(memo(ς.lbl))
        })
    }

    // output solution for each program point in order
    memo.toSeq.sortBy(_._1).map {
      case (lbl, State(_, ρ, σ, _)) ⇒
        println("-" * 10)
        println("[" + lbl + "]")
        ρ.ρ.keys.toSeq.sortBy(_.x).map((x) ⇒ println(x.x + " : " + σ(ρ(x))))
    }
  }

}

// states (with transition function)
case class State(t: Term, ρ: Env, σ: Store, κ: Kont) {

  // import the integer abstraction function
  import ALwnn.α

  // should this state be remembered?
  def memo: Boolean =
    t.isInstanceOf[StmtT]

  // if this state is a program point, return the label (undefined if
  // the state is not a program point)
  def lbl: Int =
    t match {
      case StmtT(s) ⇒ s.lbl
      case _ ⇒ sys.error("undefined")
    }

  // lattice join: t, ρ, and κ should be identical if we're at the
  // same program point, so we only need to join σ
  def ⊔(ς: State): State = {
    assert((t == ς.t) && (ρ == ς.ρ) && (κ == ς.κ))
    State(t, ρ, σ ⊔ ς.σ, κ)
  }

  // widening operator
  def ▽(ς: State): State = {
    assert((t == ς.t) && (ρ == ς.ρ) && (κ == ς.κ))
    State(t, ρ, σ ▽ ς.σ, κ)
  }

  // expression evaluation
  private def eval(e: Exp): Value = e match {
    case Range(n1, n2) ⇒ {
      // the join of all abstracted integers in the given range
      var abs = (n1 to n2).foldLeft(α(n1))((acc, n) ⇒ Z(acc ⊔ α(n)))
      Value(abs, null)
    }

    case x: Var ⇒ {
      var value = σ(ρ(x))
      value match {
        case v: Value => v
        case _ => sys.error("Inconceivable")
      }
    }
    
    // To do - Change this to use projection instead.
    case Binop(op, e1, e2) ⇒
      op match {
        case ⌜+⌝ ⇒ {
          var value = eval(e1) + eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        
        case ⌜−⌝ ⇒ {
          var value = eval(e1) − eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜×⌝ ⇒ {
          var value = eval(e1) × eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        
        case ⌜÷⌝ ⇒ {
          var value = eval(e1) ÷ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        
        case ⌜=⌝ ⇒ {
          var value = eval(e1) ≈ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜≠⌝ ⇒ {
          var value = eval(e1) ≠ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜<⌝ ⇒ {
          var value = eval(e1) < eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜≤⌝ ⇒ {
          var value = eval(e1) ≤ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜∧⌝ ⇒ {
          var value = eval(e1) ∧ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
        case ⌜∨⌝ ⇒ {
          var value = eval(e1) ∨ eval(e2)
          value match {
            case v: Value => v
            case _ => sys.error("Inconceivable")
          }
        }
      }

    case f: Fun ⇒
      val ρc = ρ filter (f.free contains _)
      Value(Z.⊥, Set(Closure(ρc, f)))
  }

  // state transition function.
  //
  // note that for any rule that uses eval, we need to check if the
  // returned abstract value can represent at least one concrete
  // integer or not——if the eval was undefined (e.g., division by
  // zero) then the rule is invalid and shouldn't return any new
  // states. we use the '.notEmpty' predicate for this check.
  //
  def next: Set[State] = t match {
    case StmtT(stmt) ⇒ stmt match {
      case e: Exp ⇒
        val v = eval(e)
        if (v.notEmpty) State(eval(e), ρ, σ, κ)
        else Set()

      case Seq(s :: rest) ⇒
        State(s, ρ, σ, seqK(rest, κ))

      case If(e: Exp, s1: Stmt, s2: Stmt) ⇒
        val guard = eval(e)
        if (guard.definitelyTrue)
          State(s1, ρ, σ, κ)
        else if (guard.definitelyFalse)
          State(s2, ρ, σ, κ)
        else if (guard.notEmpty)
          Set(State(s1, ρ, σ, κ), State(s2, ρ, σ, κ))
        else
          Set()

      case While(e: Exp, s: Stmt) ⇒
        val guard = eval(e)
        if (guard.definitelyTrue)
          State(s, ρ, σ, whileK(e, s, κ))
        else if (guard.definitelyFalse)
          State(guard, ρ, σ, κ)
        else if (guard.notEmpty)
          Set(State(s, ρ, σ, whileK(e, s, κ)), State(guard, ρ, σ, κ))
        else
          Set()

      case Assign(x: Var, e: Exp) ⇒
        val v = eval(e)
        if (v.notEmpty) State(v, ρ, σ + (ρ(x) → v), κ)
        else Set()

      case Decl(xs, s) ⇒
        val as = xs map ((x: Var) ⇒ Address(x.lbl))
        val σ1 = σ ++ (as map (_ → Value(α(0), null)))
        State(s, ρ ++ (xs zip as), σ1, κ)

      case _ ⇒ // only reached if empty Seq (should be impossible)
        Set()
    }

    case ValueT(v) ⇒ κ match {
      case seqK(s :: rest, κc) ⇒
        State(s, ρ, σ, seqK(rest, κc))

      case seqK(_, κc) /* empty sequence */ ⇒
        State(v, ρ, σ, κc)

      case whileK(e, s, κc) ⇒
        val guard = eval(e)
        if (guard.definitelyTrue)
          State(s, ρ, σ, whileK(e, s, κc))
        else if (guard.definitelyFalse)
          State(guard, ρ, σ, κc)
        else if (guard.notEmpty)
          Set(State(s, ρ, σ, whileK(e, s, κc)), State(guard, ρ, σ, κc))
        else
          Set()

      case haltK ⇒
        Set()
    }
  }

  // implicit conversions
  implicit def stmt2term(s: Stmt): Term = StmtT(s)
  implicit def val2term(v: Value): Term = ValueT(v)
  implicit def st82st8s(ς: State): Set[State] = Set(ς)

}
