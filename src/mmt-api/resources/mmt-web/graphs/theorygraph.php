<? header("Access-Control-Allow-Origin: *"); ?>
<!DOCTYPE html>
<html><head>

<meta http-equiv="content-type" content="text/html; charset=windows-1252">
  <title>Network | Basic usage</title>

  
    <link href="https://cdnjs.cloudflare.com/ajax/libs/vis/4.18.1/vis.css" rel="stylesheet" type="text/css">
	<link href="css/styles.css" rel="stylesheet" type="text/css">
  
	<script type="text/javascript" src="https://cdnjs.cloudflare.com/ajax/libs/vis/4.18.1/vis.js"></script>
	<script type="text/javascript" src="https://code.jquery.com/jquery-3.1.1.min.js"></script>
	<script type="text/javascript" src="js/theoryGraph.js"></script>
	<script type="text/javascript" src="js/globalFuncs.js"></script>
	<script type="text/javascript" src="js/globalOptions.js"></script>
	<script type="text/javascript" src="js/Optimizer.js"></script>
	
</head>
<body >

<p>
</p>

	<ul class='custom-menu' style="z-index:100">
		<li data-action="first">Open in new window</li>
	</ul>
	

	
<div id="mynetwork"><div class="vis-network" style="position: relative; overflow: hidden; -moz-user-select: none; width: 100%; height: 100%;" tabindex="900">
<canvas style="position: relative; -moz-user-select: none; width: 100%; height: 100%;" width="1200" height="800"></canvas></div></div>

<span id='string_span' style='font-size: 17px; diyplay:none;top:-1000px;left:-1000px;positon:absolute;'></span>
		

		
		
		
  <script type="text/javascript" src="https://cdnjs.cloudflare.com/ajax/libs/vis/4.18.1/vis.js"></script>
  <link href="https://cdnjs.cloudflare.com/ajax/libs/vis/4.18.1/vis.css" rel="stylesheet" type="text/css">
	<script type="text/javascript" src="https://code.jquery.com/jquery-3.1.1.min.js"></script>

    <script type="text/javascript">
		
		$(document).bind("contextmenu", function (event) 
		{
			// Avoid the real menu
			event.preventDefault();
		});
		
		
		theoryGraph=new TheoryGraph();
		theoryGraph.getGraph(getParameterByName("uri"));
    </script>
    



</body></html>