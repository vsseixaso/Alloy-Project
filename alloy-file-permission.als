module FilePermissions

-- *** Signatures *** 

-- Permission Denifiotin
abstract sig Permission {
	priority: Int
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
	
	-- This is just a test
	all directory : Directory | validContentPermissions[directory]
}
--

-- *** Execution ***
pred show[] {}

run show for 5
--
