import Init

#eval r#"before
import DerivedAlgGeo.Fixture.Leaf
class Fake
after"#

#eval r##"before #" is not a closing delimiter
import DerivedAlgGeo.Fixture.Leaf
class Fake
after"##
