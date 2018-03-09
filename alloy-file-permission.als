module FilePermissions

-- *** Signatures *** 

-- Permission Denifinition
abstract sig Permission {
	private priority: Int
}

one sig Read extends Permission {} {
	priority = 1 
}

one sig ReadWrite extends Permission {} {
	priority = 2
}

one sig Owner extends Permission {} {
	priority = 3
}
--

-- Path Definition
abstract sig Path {
	forAllPermission      : one Permission,
	externalPermission    : one Permission,
	thisComputerPermission: one Permission
}

sig Directory extends Path {
	content: set Path
}

sig File extends Path {}
--

fun parent [ent:Path]: Directory {
	ent.~content
}

-- *** Predicates ***

pred isRoot[directory : Directory] {
	no directory.~content
}

pred validComparison[parentPermission : Permission, childPermission : Permission] {
	parentPermission.priority >= childPermission.priority
}

pred validInheritancePermissons[parent : Path, child : Path] {
	validComparison[parent.forAllPermission, child.forAllPermission] and
	validComparison[parent.externalPermission, child.externalPermission] and
	validComparison[parent.thisComputerPermission, child.thisComputerPermission]
}

pred validContentPermissions[parent : Directory] {
	all child : parent.content | validInheritancePermissons[parent, child]
}
--

-- *** Facts ***

fact TreeStructure {
	-- there must be exactly one root directory
	one directory : Directory | isRoot[directory]

	-- there must be no cyclic relation between directories
	no directory : Directory | directory in directory.^content
	
	-- directories must be content of none or exaclty one directory
	all directory : Directory | lone directory.~content

	-- files must be content of exactly one direct directory
	all file : File | one file.~content
	
	all directory : Directory | validContentPermissions[directory]
}
--
/*
Test if properties of tree are being fullfilled by all the entities.
*/
assert checkTree {
	one dir: Directory | isRoot[dir] and no parent[dir]
	
	all dir :Directory | not dir in dir.content

	all path: Path | #(parent[path]) = 1 or isRoot[path]
}

check checkTree

-- *** Execution ***
pred show[] {}

run show for 5
--
