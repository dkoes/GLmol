//dkoes - calls protein surface as a webworker, returns the faces and vertices


importScripts("MarchingCubeData.js");
importScripts("ProteinSurface4.js");
self.onmessage = function(oEvent) {
	var obj = oEvent.data;
	var type = obj.type;
    var ps = new ProteinSurface(); 
    ps.initparm(obj.expandedExtent, (type == 1) ? false : true);
    ps.fillvoxels(obj.atoms, obj.extendedAtoms);
    ps.buildboundary();
    
    if (type == 4 || type == 2) ps.fastdistancemap();
    if (type == 2) {ps.boundingatom(false); ps.fillvoxelswaals(obj.atoms, obj.extendedAtoms);}
    
    ps.marchingcube(type);
    ps.laplaciansmooth(1);
    var VandF = ps.getFacesAndVertices(obj.atoms, obj.atomsToShow);    
    self.postMessage(VandF);
};


