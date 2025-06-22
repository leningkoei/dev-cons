object Main extends App {

  val string = scala.io.StdIn.readLine

  def f (list: List[Char]) : List[Char] = {
    if (list.length >= 2) {
      val fst::snd::rest = list
      fst :: f (rest)
    } else {
      List ()
    }
  }

  println(f(string.toList).mkString)
}
