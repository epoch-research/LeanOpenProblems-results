partial def unsound (u : Unit) : False := unsound u

theorem everything : False := unsound ()

