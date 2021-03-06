var serverBaseURL = "/";
var serverUrl = (typeof serverBaseURL == "undefined" || serverBaseURL==undefined) ? ((window.location.protocol=='file:')? "/" : "/mh/mmt/") : serverBaseURL;
if (location.hostname === "localhost" || location.hostname === "127.0.0.1" || location.hostname === "")
	serverUrl="/";

// URL for getting menu-entries in side-menu
var menuEntriesURL=serverUrl+":jgraph/menu?id=";

// URL parts for getting graphdata, construction looks like:
// graphDataURL + graphDataURLTypeParameterName + concreteTypeValue + "&" + graphDataURLDataParameterName + concreteGraphdataValue
var graphDataURL=serverUrl+":jgraph/json?";
// For Backend
var graphDataURLTypeParameterName = "key=";
var graphDataURLDataParameterName = "uri=";
// For TGView
var graphDataURLTypeParameterNameTGView = "type=";
var graphDataURLDataParameterNameTGView = "graphdata=";

// Colors to select for colorizing nodes in graph 
var colorizingNodesArray = ["#CCCCFF", "#FFFFCC", "#FFCC99", "#CCFFCC", "#DDDDDD", "#FFCCCC"];


// Options for theory-graph in general
var THEORY_GRAPH_OPTIONS = 
{
	physics: 
	{	
		enabled: false,
		stabilization: true,
		solver: 'barnesHut',			
		"barnesHut": 
		{
			"avoidOverlap": 1
		},
		stabilization: 
		{
			enabled: true,
			iterations: 5			// maximum number of iteration to stabilize
		}
	},
	interaction:
	{
		multiselect: true
	},
	nodes: 
	{
		physics:false,
		shapeProperties: 
		{
			useImageSize: true,  // only for image and circularImage shapes
			useBorderWithImage: true  // only for image shape
		}
	},
	edges: 
	{
		smooth: 
		{
			enabled: true,
			type: "straightCross",
			roundness: 0.3
		}
	}
	/*layout: 
	{
		hierarchical: 
		{
			sortMethod: "directed",
			direction: "LR"
		}
	}*/
};

// All available arrow styles
var ARROW_STYLES=
{
	"include":
	{
		color:"#cccccc",
		colorHighlight:"#cccccc",
		colorHover:"#cccccc",
		dashes: false,
		circle:false,
		directed: true,
		smoothEdge: true,
		width: 1
	},
	"modelinclude":
	{
		color:"black",
		colorHighlight:"black",
		colorHover:"black",
		dashes: false,
		circle:false,
		directed: false,
		smoothEdge: false,
		width: 1
	},
	"meta":
	{
		color:"green",
		colorHighlight:"green",
		colorHover:"green",
		dashes: true,
		circle: true,
		directed: true,
		smoothEdge: true,
		width: 1
	},
	"alignment":
	{
		color:"red",
		colorHighlight:"red",
		colorHover:"red",
		dashes: true,
		circle: false,
		directed: false,
		smoothEdge: true,
		width: 1
	},
	"view":
	{
		color:"black",
		colorHighlight:"black",
		colorHover:"black",
		dashes: false,
		circle:false,
		directed: true,
		smoothEdge: true,
		width: 1
	},
	"structure":
	{
		color:"#cccccc",
		colorHighlight:"#cccccc",
		colorHover:"#cccccc",
		dashes: true,
		circle:false,
		directed: true,
		smoothEdge: true,
		width: 1
	}
};


// All available node styles
var NODE_STYLES =
{
	"model":
	{
		shape: "square",
		color: "#DDDDDD",
		colorBorder: "#222222",
		colorHighlightBorder: "#444444",
		colorHighlight: "#EEEEEE",
		dashes: false
	},
	"border":
	{
		shape: "circle",
		color: "#E8E8E8",
		colorBorder: "#D8D8D8",
		colorHighlightBorder: "#A8A8A8",
		colorHighlight: "#D8D8D8",
		dashes: false
	},
	"theory":
	{
		shape: "circle",
		color: "#D2E5FF",
		colorBorder: "#2B7CE9",
		colorHighlightBorder: "#2B7CE9",
		colorHighlight: "#D2E5FF",
		dashes: false
	}
};

// All available graph types (for MMT menu)
var GRAPH_TYPES =
[
	{
		id: "thgraph",
		menuText: "Th. Graph",
		tooltip: ""
	},
	{
		id: "pgraph",
		menuText: "P Graph",
		tooltip: ""
	},
	{
		id: "docgraph",
		menuText: "Doc Graph",
		tooltip: ""
	},
	{
		id: "archivegraph",
		menuText: "Archive Graph",
		tooltip: ""
	},
	{
		id: "mpd",
		menuText: "MPD Graph",
		tooltip: "MPD Graph-Viewer"
	}
];

