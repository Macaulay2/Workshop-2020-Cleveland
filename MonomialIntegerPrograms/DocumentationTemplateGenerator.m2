newPackage (
  "DocumentationTemplateGenerator",
  Version=>"0.1",
  Authors => {{
      Name => "Jay White", 
      Email => "jay.white@uky.edu"
      }},
  Headline => "A package designed to generate documentation for packages."
)

export {
    "generateFunctionCallTemplate",
    "generateFullPackageTemplate"
    }

indent = "    ";
generateSubindent = method();
generateSubindent (List) := L -> stack for p in L list (
    p#0,
    indent | p#1
);
generateGeneric = method();
generateGeneric (List) := L -> stack(
  "doc ///",
  indent | generateSubindent(L),
  "///"
);
descriptionTemplate = ("Description" => generateSubindent{
  "Text" => "TODO: explanatory prose",
  "Example" => "example = 1 + 1"||"example * 3",
  "Text" => "TODO: more explanatory prose"});
generatePackageHeaderTemplate = method(TypicalValue=>Net);
generatePackageHeaderTemplate (String) := packageName -> generateGeneric{
  "Key" => packageName,
  "Headline" => "one line description",
  descriptionTemplate,
  "Caveat" => "warning",
  "Subnodes" => "functionName1"||"functionName2"
};
generateFunctionCallTemplate = method(TypicalValue=>Net);
generateFunctionCallTemplate (List, String) := (functionCall, typicalValue) -> generateGeneric {
  "Key" => "(" | demark(", ", functionCall) | ")",
  "Headline" => "one line description if different from " | functionCall#0,
  "Usage" => "outName = " | functionCall#0 | 
              "(" | demark(", ",(1..#functionCall-1)/(i->"inName"|i)) | ")",
  "Inputs" => generateSubindent for i from 1 to #functionCall-1 list (
    "inName"|i|":"|functionCall#i => "description of input"
  ),
  "Outputs" => generateSubindent{"outName:" | typicalValue=> "description of output"},
  "Consequences" => generateSubindent{"Item" => "consequence of function"},
  descriptionTemplate,
  "Caveat" => "warning"
}
generateFunctionCallTemplate (List) := functionCall -> (
  typicalValue :=
    if typicalValues#?(functionCall#0) then 
      typicalValues#(functionCall#0)
    else 
      "OutType";
  generateFunctionCallTemplate(toString\functionCall, toString typicalValue)
)
generateAllFunctionCalls = method(TypicalValue=>Net);
generateAllFunctionCalls (Thing) := f -> stack for fC in methods(f) list 
  generateFunctionCallTemplate toList fC;

generateFunctionNameTemplate = method(TypicalValue=>Net);
generateFunctionNameTemplate (String, String) := (functionName, typicalValue) -> generateGeneric {
  "Key" => functionName,
  "Headline" => "one line description",
  "Usage" => "usage",
  "Inputs" => generateSubindent {
    "inName:InType" => "description of input"
  },
  "Outputs" => generateSubindent{"outName:" | typicalValue=> "description of output"},
  "Consequences" => generateSubindent{"Item" => "consequence of function"},
  descriptionTemplate,
  "Caveat" => "warning"
}
generateFunctionNameTemplate (Thing) := f-> (
  typicalValue :=
    if typicalValues#?f then 
      typicalValues#f
    else 
      "OutType";
  generateFunctionNameTemplate(toString f, toString typicalValue)
)

generateFullFunctionTemplate = method(TypicalValue=>Net);
generateFullFunctionTemplate (Thing) := f -> if #methods(f) == 1 then (
    generateAllFunctionCalls f
  ) else (
    (generateFunctionNameTemplate f) || (generateAllFunctionCalls f)
  )
  

generateFullPackageTemplate = method(TypicalValue=>Net);
generateFullPackageTemplate (Package) := p -> (
  functions := select(value\(sort p#"exported symbols"), v->instance(v,Function));
  stack flatten(generatePackageHeaderTemplate(toString p), for f in functions list generateFullFunctionTemplate(f))
)
end--
installPackage("DocumentationTemplateGenerator");
needsPackage("DocumentationTemplateGenerator");
generateFullPackageTemplate(DocumentationTemplateGenerator)
