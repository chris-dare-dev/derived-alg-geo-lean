import Init

#eval s!"{r#"before
import DerivedAlgGeo.Fixture.Leaf
class Fake
after"#}"

#eval s!"prefix {r##"before
import DerivedAlgGeo.Fixture.Leaf
class Fake
after"##} suffix"
