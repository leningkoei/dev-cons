import scala.io.StdIn

object Main {
  def main(args: Array[String]): Unit = {
    val fuck = StdIn.readLine();
    println(fuck);
  }
}

class Point(var x: Int, var y: Int) {

  private var _x = 0
  private var _y = 0
  private val bound = 100

  def move(dx: Int, dy: Int): Unit = {
    x = x + dx
    y = y + dy
  }

  override def toString: String = s"($x, $y)"
}

trait Iterator {
  type T
  def hasNext: Boolean
  def next(): T
}

trait ForEachAble extends Iterator {
  def forEach (f: T => Unit): Unit = {
    while (hasNext) {
      f (next ())
    }
  }
}

class StringIterator(s: String) extends Iterator {
  type T = Char
  private var i = 0
  override def hasNext = i < s.length
  override def next() = {
    val ch = s charAt i
    i += 1
    ch
  }
}

class ForEachAbleString(s: String) extends StringIterator(s) with ForEachAble {
}
