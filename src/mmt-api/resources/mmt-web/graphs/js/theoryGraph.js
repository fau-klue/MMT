function TheoryGraph()
{
	var originalNodes = null;
	var originalEdges = null;
	var network = null;
	var clusterId=0;
	var nodes;
	var edges;
	var lastClusterZoomLevel = 0;
    var clusterFactor = 1;
	var that=this;
	var zoomClusters=[];
	
	this.downloadCanvasAsImage = function(button)
	{
		var minX=111110;
		var minY=111110;
		var maxX=-111110;
		var maxY=-111110;
		for (var i = 0; i < originalNodes.length; i++) 
		{
			var curNode = originalNodes[i];
			var nodePosition = network.getPositions([curNode.id]);
			
			minX=Math.min(nodePosition[curNode.id].x,minX);
			maxX=Math.max(nodePosition[curNode.id].x,maxX);
			
			minY=Math.min(nodePosition[curNode.id].y,minY);
			maxY=Math.max(nodePosition[curNode.id].y,maxY);
		}
		
		var originalWidth=network.canvas.frame.canvas.width;
		var originalHeight=network.canvas.frame.canvas.height;
		
		network.setSize((maxX-minX)*1.2,(maxY-minY)*1.2);
		
		network.redraw();
		network.fit();
		
		network.once("afterDrawing",function () 
		{
			//button.href = network.canvas.frame.canvas.toDataURL();
			//button.download = "graph.png";
			var image=network.canvas.frame.canvas.toDataURL("image/png")
			window.open(image);
			network.setSize(originalWidth,originalHeight);
			network.redraw();
			network.fit();
		});
	}
	
    function openOutlierClusters(scale) 
	{
        var newClusters = [];
        var declustered = false;
        for (var i = 0; i < zoomClusters.length; i++) 
		{
            if (zoomClusters[i].scale < scale) 
			{
                network.openCluster(zoomClusters[i].id);
                lastClusterZoomLevel = scale;
                declustered = true;
            }
            else 
			{
                newClusters.push(zoomClusters[i])
            }
        }
        zoomClusters = newClusters;
    }
	
	this.clusterOutliers=function(scale)
	{
		var clusterOptionsByData = 
		{
			processProperties: function (clusterOptions, childNodes) 
			{
				clusterId = clusterId + 1;
				var childrenCount = 0;
				for (var i = 0; i < childNodes.length; i++) 
				{
					childrenCount += childNodes[i].childrenCount || 1;
				}
				clusterOptions.childrenCount = childrenCount;
				clusterOptions.label = "# " + childrenCount + "";
				clusterOptions.font = {size: Math.min(childrenCount+20,40)}
				clusterOptions.id = 'cluster_' + clusterId;
				zoomClusters.push({id:'cluster_' + clusterId, scale:scale});
				return clusterOptions;
			},
			clusterNodeProperties: {borderWidth: 2, shape: 'database', color:"orange"}
		}
		network.clusterOutliers(clusterOptionsByData);
	}
	
	this.selectNodesInRect = function(rect) 
	{
		var fromX;
		var toX;
		var fromY;
		var toY;
		var nodesIdInDrawing = [];
		var xRange = getStartToEnd(rect.startX, rect.w);
		var yRange = getStartToEnd(rect.startY, rect.h);

		for (var i = 0; i < originalNodes.length; i++) 
		{
			var curNode = originalNodes[i];
			var nodePosition = network.getPositions([curNode.id]);
			var nodeXY = network.canvasToDOM({x: nodePosition[curNode.id].x, y: nodePosition[curNode.id].y});
			if (xRange.start <= nodeXY.x && nodeXY.x <= xRange.end && yRange.start <= nodeXY.y && nodeXY.y <= yRange.end) 
			{
				nodesIdInDrawing.push(curNode.id);
			}
		}
		network.selectNodes(nodesIdInDrawing);
	}
	
	this.cluster = function(nodeIds,name)
	{
		if(nodeIds==undefined)
		{
			nodeIds=network.getSelectedNodes();
		}
		
		if(name==undefined)
		{
			name='cluster_' +clusterId;
		}
		
		if(network!=null)
		{
			var options = 
			{
				joinCondition:function(nodeOptions) 
				{
					return nodeIds.indexOf(nodeOptions.id) != -1;
				},
				processProperties: function (clusterOptions, childNodes, childEdges) 
				{
                  var totalMass = 0;
                  for (var i = 0; i < childNodes.length; i++) 
				  {
                      totalMass += childNodes[i].mass;
                  }
                  clusterOptions.mass = totalMass;
                  return clusterOptions;
              },
              clusterNodeProperties: {id: 'cluster_' +clusterId , borderWidth: 2, shape: 'database', color:"orange", label:name}
			}

			network.clustering.cluster(options);
			clusterId++;
		}
	}
	
	this.getGraph= function(jsonURL)
	{
		document.body.style.cursor = 'wait';
		$.get(jsonURL, drawGraph);
	}

	function drawGraph(data, status)
	{
		originalNodes=data["nodes"];
		originalEdges=data["edges"];
		
		ensureUniqueIds(originalNodes);
		ensureUniqueIds(originalEdges);
		
		postprocessEdges();
		
		startRendering();
	}
	
	function postprocessEdges()
	{
		for(var i=0;i<originalEdges.length;i++)
		{
			if(originalEdges[i].style!=undefined && ARROW_STYLES[originalEdges[i].style]!=undefined)
			{
				var styleInfos=ARROW_STYLES[originalEdges[i].style];
				originalEdges[i].arrows = {to:{enabled:styleInfos.directed}};
				
				if(styleInfos.circle==true)
				{
					originalEdges[i].arrows.to.type="circle";
				}
				else
				{
					originalEdges[i].arrows.to.type="arrow";
				}

				originalEdges[i].dashes=styleInfos.dashes;
				originalEdges[i].color={color:styleInfos.color, highlight:styleInfos.colorHighlight, hover:styleInfos.colorHover};
			}
		}
	}
	
	function ensureUniqueIds(arrays)
	{
		var idArray=[];
		for(var i=0;i<arrays.length;i++)
		{
			if(idArray[arrays[i]["id"]]==undefined)
			{
				idArray[arrays[i]["id"]]=1;
			}
			else
			{
				arrays[i]["id"]+="_"+i;
				idArray[arrays[i]["id"]]=1;
			}
		}
	}
	
	// Called when the Visualization API is loaded.
	function startRendering() 
	{
		if(THEORY_GRAPH_OPTIONS.layout==undefined)
		{
			var opti=new Optimizer(originalNodes,originalEdges);
			opti.GenerateRandomSolution();
			opti.SolveUsingForces(1000);
		}
		
		nodes = new vis.DataSet(originalNodes);
		edges = new vis.DataSet(originalEdges);
		
		// create a network
		var container = document.getElementById('mynetwork');
		var data = 
		{
			nodes: nodes,
			edges: edges
		};
		
		network = new vis.Network(container, data, THEORY_GRAPH_OPTIONS);
		//network.startSimulation(10);
		
		if(THEORY_GRAPH_OPTIONS.physics.enabled==false)
		{
			document.body.style.cursor = 'auto';
		}
		
		// If the document is clicked somewhere
		network.on("click", function (e) 
		{
			// If the clicked element is not the menu
			if (!$(e.target).parents(".custom-menu").length > 0) 
			{
				// Hide it
				$(".custom-menu").hide(10);
			}
		});
		
		// If the menu element is clicked
		$(".custom-menu li").click(function()
		{
			var nodesFound=network.getSelectedNodes();
			var selectedNode=undefined;
			
			for(var i=0;i<originalNodes.length;i++)
			{
				if(originalNodes[i]["id"]==nodesFound[0])
				{
					selectedNode=originalNodes[i];
					break;
				}
			}
			
			var edgesFound=network.getSelectedEdges();
			var selectedEdge=undefined;
			for(var i=0;i<originalEdges.length;i++)
			{
				if(originalEdges[i]["id"]==edgesFound[0])
				{
					selectedEdge=originalEdges[i];
					break;
				}
			}
			
			var selected=undefined;
			
			if(selectedEdge!=undefined)
			{
				selected=selectedEdge;
			}
			
			if(selectedNode!=undefined)
			{
				selected=selectedNode;
			}
			
			
			if(selected!=undefined)
			{
				// This is the triggered action name
				switch($(this).attr("data-action")) 
				{
					// A case for each action
					case "first": window.open(selected["url"]); break;
				}
			}
			
			// Hide it AFTER the action was triggered
			$(".custom-menu").hide(10);
		});
		
		network.on("oncontext", function (params) 
		{
			var node=network.getNodeAt({x: params["pointer"]["DOM"]["x"],y: params["pointer"]["DOM"]["y"]});
			
			if(node!=undefined)
			{
				network.selectNodes([node]);
				// Show contextmenu
				$(".custom-menu").finish().show(10).
				
				// In the right position (the mouse)
				css({
					top: params["pointer"]["DOM"]["y"]*1+20 + "px",
					left: params["pointer"]["DOM"]["x"]*1+16 + "px"
				});
				return;
			}
			
			var edge=network.getEdgeAt({x: params["pointer"]["DOM"]["x"],y: params["pointer"]["DOM"]["y"]});
			
			if(edge!=undefined)
			{
				network.selectEdges([edge]);
				// Show contextmenu
				$(".custom-menu").finish().show(10).
				
				// In the right position (the mouse)
				css({
					top: params["pointer"]["DOM"]["y"]*1+20 + "px",
					left: params["pointer"]["DOM"]["x"]*1+16 + "px"
				});
			}
			
		});
		
		network.on("stabilizationIterationsDone", function (params) 
		{
			network.stopSimulation();
			var options = 
			{
				physics: 
				{
					enabled: false
				}
			};
			network.setOptions(options);
			document.body.style.cursor = 'auto';
		});
		
		
		// we use the zoom event for our clustering
		/*network.on('zoom', function (params) 
		{
			console.log(params.direction+" "+params.scale+" < "+lastClusterZoomLevel*clusterFactor);
			if (params.direction == '-') 
			{
				if (params.scale < lastClusterZoomLevel*clusterFactor) 
				{
					that.clusterOutliers(params.scale);
					lastClusterZoomLevel = params.scale;
				}
			}
			else 
			{
				openOutlierClusters(params.scale);
			}
		});*/
		
		network.once('initRedraw', function() 
		{
			if (lastClusterZoomLevel === 0) 
			{
				lastClusterZoomLevel = network.getScale();
			}
		});
	}
}