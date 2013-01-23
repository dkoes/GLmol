/*  ProteinSurface.js by biochem_fan

Ported and modified for Javascript based on EDTSurf,
  whose license is as follows.

Permission to use, copy, modify, and distribute this program for any
purpose, with or without fee, is hereby granted, provided that this
copyright notice and the reference information appear in all copies or
substantial portions of the Software. It is provided "as is" without
express or implied warranty. 

Reference:
http://zhanglab.ccmb.med.umich.edu/EDTSurf/
D. Xu, Y. Zhang (2009) Generating Triangulated Macromolecular Surfaces
by Euclidean Distance Transform. PLoS ONE 4(12): e8140.

=======

TODO: Improved performance on Firefox
      Reduce memory consumption
      Refactor!
 */

// dkoes
// Surface calculations.  This must be safe to use within a web worker.
if (typeof console === 'undefined') {
	// this should only be true inside of a webworker
	console = {
		log : function() {
		}
	};
}

var ProteinSurface = (function() {
	// constants for vpbits bitmasks
	var INOUT = 1;
	var ISDONE = 2;
	var ISBOUND = 4;

	var ptranx = 0, ptrany = 0, ptranz = 0;
	var boxLength = 128;
	var probeRadius = 1.4, scaleFactor = 1;
	var pHeight = 0, pWidth = 0, pLength = 0;
	var cutRadius = 0;
	var vpBits = null; // uint8 array of bitmasks
	var vpDistance = null; // floatarray
	var vpAtomID = null; // intarray
	var vertnumber = 0, facenumber = 0;
	var pminx = 0, pminy = 0, pminz = 0, pmaxx = 0, pmaxy = 0, pmaxz = 0;
	var rasrad = [ 1.90, 1.88, 1.63, 1.48, 1.78, 1.2, 1.87, 1.96, 1.63, 0.74,
			1.8, 1.48, 1.2 ];// liang
	// Calpha c n o s h p Cbeta ne fe other ox hx

	var depty = new Array(13), widxz = new Array(13);
	var fixsf = 2;
	var faces, verts;
	var nb = [ [ 1, 0, 0 ], [ -1, 0, 0 ], [ 0, 1, 0 ], [ 0, -1, 0 ],
			[ 0, 0, 1 ], [ 0, 0, -1 ], [ 1, 1, 0 ], [ 1, -1, 0 ], [ -1, 1, 0 ],
			[ -1, -1, 0 ], [ 1, 0, 1 ], [ 1, 0, -1 ], [ -1, 0, 1 ],
			[ -1, 0, -1 ], [ 0, 1, 1 ], [ 0, 1, -1 ], [ 0, -1, 1 ],
			[ 0, -1, -1 ], [ 1, 1, 1 ], [ 1, 1, -1 ], [ 1, -1, 1 ],
			[ -1, 1, 1 ], [ 1, -1, -1 ], [ -1, -1, 1 ], [ -1, 1, -1 ],
			[ -1, -1, -1 ] ];

	// define our own faces and vectors to avoid pulling on THREE for the
	// webworker
	var Vector3 = function(x, y, z) {
		this.x = x || 0;
		this.y = y || 0;
		this.z = z || 0;
	};

	var Face3 = function(a, b, c) {
		this.a = a;
		this.b = b;
		this.c = c;
	};

	this.getFacesAndVertices = function(atoms, atomlist) {
		var atomsToShow = new Object();
		for ( var i = 0, lim = atomlist.length; i < lim; i++)
			atomsToShow[atomlist[i]] = true;
		var vertices = verts;
		for (i = 0; i < vertices.length; i++) {
			vertices[i].x = vertices[i].x / scaleFactor - ptranx;
			vertices[i].y = vertices[i].y / scaleFactor - ptrany;
			vertices[i].z = vertices[i].z / scaleFactor - ptranz;
		}

		var finalfaces = []
		for ( var i = 0; i < faces.length; i++) { 
			var f = faces[i];
			if(f.a == f.b && f.b == f.c)
				continue;
			var a = vertices[f.a].atomid, b = vertices[f.b].atomid, c = vertices[f.c].atomid;
			if (!atomsToShow[a] && !atomsToShow[b] && !atomsToShow[c]) {
				continue;
			}			

			finalfaces.push(f);
		}
		return {
			vertices : vertices,
			faces : finalfaces
		};
	};

	this.laplaciansmooth = function(numiter) {
		var tps = new Array(verts.length);
		for ( var i = 0; i < verts.length; i++)
			tps[i] = {
				x : 0,
				y : 0,
				z : 0
			};
		var vertdeg = new Array(20);
		var flagvert;
		for ( var i = 0; i < 20; i++)
			vertdeg[i] = new Array(verts.length);
		for ( var i = 0; i < verts.length; i++)
			vertdeg[0][i] = 0;
		for ( var i = 0; i < faces.length; i++) {
			flagvert = true;
			for ( var j = 0; j < vertdeg[0][faces[i].a]; j++) {
				if (faces[i].b == vertdeg[j + 1][faces[i].a]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].a]++;
				vertdeg[vertdeg[0][faces[i].a]][faces[i].a] = faces[i].b;
			}
			flagvert = true;
			for ( var j = 0; j < vertdeg[0][faces[i].a]; j++) {
				if (faces[i].c == vertdeg[j + 1][faces[i].a]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].a]++;
				vertdeg[vertdeg[0][faces[i].a]][faces[i].a] = faces[i].c;
			}
			// b
			flagvert = true;
			for (j = 0; j < vertdeg[0][faces[i].b]; j++) {
				if (faces[i].a == vertdeg[j + 1][faces[i].b]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].b]++;
				vertdeg[vertdeg[0][faces[i].b]][faces[i].b] = faces[i].a;
			}
			flagvert = true;
			for (j = 0; j < vertdeg[0][faces[i].b]; j++) {
				if (faces[i].c == vertdeg[j + 1][faces[i].b]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].b]++;
				vertdeg[vertdeg[0][faces[i].b]][faces[i].b] = faces[i].c;
			}
			// c
			flagvert = true;
			for (j = 0; j < vertdeg[0][faces[i].c]; j++) {
				if (faces[i].a == vertdeg[j + 1][faces[i].c]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].c]++;
				vertdeg[vertdeg[0][faces[i].c]][faces[i].c] = faces[i].a;
			}
			flagvert = true;
			for (j = 0; j < vertdeg[0][faces[i].c]; j++) {
				if (faces[i].b == vertdeg[j + 1][faces[i].c]) {
					flagvert = false;
					break;
				}
			}
			if (flagvert) {
				vertdeg[0][faces[i].c]++;
				vertdeg[vertdeg[0][faces[i].c]][faces[i].c] = faces[i].b;
			}
		}

		var wt = 1.00;
		var wt2 = 0.50;
		var ssign;
		var outwt = 0.75 / (scaleFactor + 3.5); // area-preserving
		for ( var k = 0; k < numiter; k++) {
			for ( var i = 0; i < verts.length; i++) {
				if (vertdeg[0][i] < 3) {
					tps[i].x = verts[i].x;
					tps[i].y = verts[i].y;
					tps[i].z = verts[i].z;
				} else if (vertdeg[0][i] == 3 || vertdeg[0][i] == 4) {
					tps[i].x = 0;
					tps[i].y = 0;
					tps[i].z = 0;
					for (j = 0; j < vertdeg[0][i]; j++) {
						tps[i].x += verts[vertdeg[j + 1][i]].x;
						tps[i].y += verts[vertdeg[j + 1][i]].y;
						tps[i].z += verts[vertdeg[j + 1][i]].z;
					}
					tps[i].x += wt2 * verts[i].x;
					tps[i].y += wt2 * verts[i].y;
					tps[i].z += wt2 * verts[i].z;
					tps[i].x /= wt2 + vertdeg[0][i];
					tps[i].y /= wt2 + vertdeg[0][i];
					tps[i].z /= wt2 + vertdeg[0][i];
				} else {
					tps[i].x = 0;
					tps[i].y = 0;
					tps[i].z = 0;
					for ( var j = 0; j < vertdeg[0][i]; j++) {
						tps[i].x += verts[vertdeg[j + 1][i]].x;
						tps[i].y += verts[vertdeg[j + 1][i]].y;
						tps[i].z += verts[vertdeg[j + 1][i]].z;
					}
					tps[i].x += wt * verts[i].x;
					tps[i].y += wt * verts[i].y;
					tps[i].z += wt * verts[i].z;
					tps[i].x /= wt + vertdeg[0][i];
					tps[i].y /= wt + vertdeg[0][i];
					tps[i].z /= wt + vertdeg[0][i];
				}
			}
			for ( var i = 0; i < verts.length; i++) {
				verts[i].x = tps[i].x;
				verts[i].y = tps[i].y;
				verts[i].z = tps[i].z;
			}
			/*
			 * computenorm(); for (var i = 0; i < vertnumber; i++) { if
			 * (verts[i].inout) ssign = 1; else ssign = -1; verts[i].x += ssign *
			 * outwt * verts[i].pn.x; verts[i].y += ssign * outwt *
			 * verts[i].pn.y; verts[i].z += ssign * outwt * verts[i].pn.z; }
			 */
		}
	};

	this.initparm = function(extent, btype) {
		var margin = 2.5;
		pminx = extent[0][0], pmaxx = extent[1][0];
		pminy = extent[0][1], pmaxy = extent[1][1];
		pminz = extent[0][2], pmaxz = extent[1][2];

		if (btype) {
			pminx -= margin;
			pminy -= margin;
			pminz -= margin;
			pmaxx += margin;
			pmaxy += margin;
			pmaxz += margin;
		} else {
			pminx -= probeRadius + margin;
			pminy -= probeRadius + margin;
			pminz -= probeRadius + margin;
			pmaxx += probeRadius + margin;
			pmaxy += probeRadius + margin;
			pmaxz += probeRadius + margin;
		}

		ptranx = -pminx;
		ptrany = -pminy;
		ptranz = -pminz;
		scaleFactor = pmaxx - pminx;
		if ((pmaxy - pminy) > scaleFactor)
			scaleFactor = pmaxy - pminy;
		if ((pmaxz - pminz) > scaleFactor)
			scaleFactor = pmaxz - pminz;
		scaleFactor = (boxLength - 1.0) / scaleFactor;

		boxLength = Math.floor(boxLength * fixsf / scaleFactor);
		scaleFactor = fixsf;
		var threshbox = 180; // maximum possible boxsize
		if (boxLength > threshbox) {
			sfthresh = threshbox / boxLength;
			boxLength = Math.floor(threshbox);
			scaleFactor = scaleFactor * sfthresh;
		}

		pLength = Math.ceil(scaleFactor * (pmaxx - pminx)) + 1;
		pWidth = Math.ceil(scaleFactor * (pmaxy - pminy)) + 1;
		pHeight = Math.ceil(scaleFactor * (pmaxz - pminz)) + 1;
		if (pLength > boxLength)
			pLength = boxLength;
		if (pWidth > boxLength)
			pWidth = boxLength;
		if (pHeight > boxLength)
			pHeight = boxLength;
		this.boundingatom(btype);
		cutRadis = probeRadius * scaleFactor;

		vpBits = new Uint8Array(pLength * pWidth * pHeight);
		vpDistance = new Float64Array(pLength * pWidth * pHeight); // float 32
		// doesn't
		// play
		// nicely
		// with
		// native
		// floats
		vpAtomID = new Int32Array(pLength * pWidth * pHeight);
		console.log("Box size: ", pLength, pWidth, pHeight, vpBits.length);
	};

	this.boundingatom = function(btype) {
		var tradius = new Array(13);
		var txz, tdept, sradius, idx;
		flagradius = btype;

		for ( var i = 0; i < 13; i++) {
			if (!btype)
				tradius[i] = rasrad[i] * scaleFactor + 0.5;
			else
				tradius[i] = (rasrad[i] + probeRadius) * scaleFactor + 0.5;

			sradius = tradius[i] * tradius[i];
			widxz[i] = Math.floor(tradius[i]) + 1;
			depty[i] = new Array(widxz[i] * widxz[i]);
			indx = 0;
			for (j = 0; j < widxz[i]; j++) {
				for (k = 0; k < widxz[i]; k++) {
					txz = j * j + k * k;
					if (txz > sradius)
						depty[i][indx] = -1; // outside
					else {
						tdept = Math.sqrt(sradius - txz);
						depty[i][indx] = Math.floor(tdept);
					}
					indx++;
				}
			}
		}
	}

	this.fillvoxels = function(atoms, atomlist) { // (int seqinit,int
		// seqterm,bool
		// atomtype,atom*
		// proseq,bool bcolor)
		var i;
		for ( var i = 0, lim = vpBits.length; i < lim; i++) {
			vpBits[i] = 0;
			vpDistance[i] = -1.0;
			vpAtomID[i] = -1;
		}

		for (i in atomlist) {
			atom = atoms[atomlist[i]];
			if (atom == undefined)
				continue;
			this.fillAtom(atom, atoms);
		}

		for (i = 0, lim = vpBits.length; i < lim; i++)
			if (vpBits[i] & INOUT)
				vpBits[i] |= ISDONE;

	};

	this.getAtomType = function(atom) {
		var at = 10;
		if (atom.atom == 'CA')
			at = 0;
		else if (atom.atom == 'C')
			at = 1;
		else if (atom.elem == 'C')
			at = 7;
		else if (atom.atom == '0')
			at = 3;
		else if (atom.elem == 'O')
			at = 11;
		else if (atom.atom == 'N')
			at = 2;
		else if (atom.elem == 'N')
			at = 8;
		else if (atom.elem == 'S')
			at = 4;
		else if (atom.elem == 'P')
			at = 6;
		else if (atom.atom == 'FE')
			at = 9;
		else if (atom.atom == 'H')
			at = 5;
		else if (atom.elem == 'H')
			at = 12;
		return at;
	};

	this.fillAtom = function(atom, atoms) {
		var cx, cy, cz, ox, oy, oz;
		cx = Math.floor(0.5 + scaleFactor * (atom.x + ptranx));
		cy = Math.floor(0.5 + scaleFactor * (atom.y + ptrany));
		cz = Math.floor(0.5 + scaleFactor * (atom.z + ptranz));

		var at = this.getAtomType(atom);
		var nind = 0;
		var cnt = 0;

		for (i = 0; i < widxz[at]; i++) {
			for (j = 0; j < widxz[at]; j++) {
				if (depty[at][nind] != -1) {
					for (ii = -1; ii < 2; ii++) {
						for (jj = -1; jj < 2; jj++) {
							for (kk = -1; kk < 2; kk++) {
								if (ii != 0 && jj != 0 && kk != 0) {
									mi = ii * i;
									mk = kk * j;
									for (k = 0; k <= depty[at][nind]; k++) {
										mj = k * jj;
										si = cx + mi;
										sj = cy + mj;
										sk = cz + mk;
										if (si < 0 || sj < 0 || sk < 0
												|| si >= pLength
												|| sj >= pWidth
												|| sk >= pHeight)
											continue;
										var index = si * pWidth * pHeight + sj
												* pHeight + sk;

										if (!(vpBits[index] & INOUT)) {
											vpBits[index] |= INOUT;
											vpAtomID[index] = atom.serial;
										} else {
											var atom2 = atoms[vpAtomID[index]];
											ox = Math.floor(0.5 + scaleFactor
													* (atom2.x + ptranx));
											oy = Math.floor(0.5 + scaleFactor
													* (atom2.y + ptrany));
											oz = Math.floor(0.5 + scaleFactor
													* (atom2.z + ptranz));
											if (mi * mi + mj * mj + mk * mk < ox
													* ox + oy * oy + oz * oz)
												vpAtomID[index] = atom.serial;
										}

									}// k
								}// if
							}// kk
						}// jj
					}// ii
				}// if
				nind++;
			}// j
		}// i
	};

	this.fillvoxelswaals = function(atoms, atomlist) {
		for ( var i = 0, lim = vpBits.length; i < lim; i++)
			vpBits[i] &= ~ISDONE; // not isdone

		for (i in atomlist) {
			atom = atoms[atomlist[i]];
			if (atom == undefined)
				continue;

			this.fillAtomWaals(atom, atoms);
		}
	};

	this.fillAtomWaals = function(atom, atoms) {
		var cx, cy, cz, ox, oy, oz, nind = 0;
		cx = Math.floor(0.5 + scaleFactor * (atom.x + ptranx));
		cy = Math.floor(0.5 + scaleFactor * (atom.y + ptrany));
		cz = Math.floor(0.5 + scaleFactor * (atom.z + ptranz));

		var at = this.getAtomType(atom);

		for (i = 0; i < widxz[at]; i++) {
			for (j = 0; j < widxz[at]; j++) {
				if (depty[at][nind] != -1) {
					for (ii = -1; ii < 2; ii++) {
						for (jj = -1; jj < 2; jj++) {
							for (kk = -1; kk < 2; kk++) {
								if (ii != 0 && jj != 0 && kk != 0) {
									mi = ii * i;
									mk = kk * j;
									for (k = 0; k <= depty[at][nind]; k++) {
										mj = k * jj;
										si = cx + mi;
										sj = cy + mj;
										sk = cz + mk;
										if (si < 0 || sj < 0 || sk < 0)
											continue;
										var index = si * pWidth * pHeight + sj
												* pHeight + sk;
										if (!(vpBits[index] & ISDONE)) {
											vpBits[index] |= ISDONE;
											vpAtomID[index] = atom.serial;
										} else {
											var atom2 = atoms[vpAtomID[index]];
											ox = Math.floor(0.5 + scaleFactor
													* (atom2.x + ptranx));
											oy = Math.floor(0.5 + scaleFactor
													* (atom2.y + ptrany));
											oz = Math.floor(0.5 + scaleFactor
													* (atom2.z + ptranz));
											if (mi * mi + mj * mj + mk * mk < ox
													* ox + oy * oy + oz * oz)
												vpAtomID[index] = atom.serial;
										}

									}// k
								}// if
							}// kk
						}// jj
					}// ii
				}// if
				nind++;
			}// j
		}// i
	};

	this.buildboundary = function() {
		for (i = 0; i < pLength; i++) {
			for (j = 0; j < pHeight; j++) {
				for (k = 0; k < pWidth; k++) {
					var index = i * pWidth * pHeight + k * pHeight + j;
					if (vpBits[index] & INOUT) {
						var flagbound = false;
						var ii = 0;
						while (!flagbound && ii < 26) {
							var ti = i + nb[ii][0], tj = j + nb[ii][2], tk = k
									+ nb[ii][1];
							if (ti > -1
									&& ti < pLength
									&& tk > -1
									&& tk < pWidth
									&& tj > -1
									&& tj < pHeight
									&& !(vpBits[ti * pWidth * pHeight + tk
											* pHeight + tj] & INOUT)) {
								vpBits[index] |= ISBOUND;
								flagbound = true;
							} else
								ii++;
						}
					}
				}
			}
		}
	};

	// a little class for 3d array, should really generalize this and
	// use throughout...
	var PointGrid = function(length, width, height) {
		// the standard says this is zero initialized
		var data = new Int32Array(length * width * height * 3);

		// set position x,y,z to pt, which has ix,iy,and iz
		this.set = function(x, y, z, pt) {
			var index = ((((x * width) + y) * height) + z) * 3;
			data[index] = pt.ix;
			data[index + 1] = pt.iy;
			data[index + 2] = pt.iz;
		};

		// return point at x,y,z
		this.get = function(x, y, z) {
			var index = ((((x * width) + y) * height) + z) * 3;
			return {
				ix : data[index],
				iy : data[index + 1],
				iz : data[index + 2]
			};
		};
	};

	this.fastdistancemap = function() {
		var positin = 0, positout = 0, eliminate = 0;
		var certificate;
		var i, j, k;
		totalsurfacevox = 0;
		totalinnervox = 0;

		var boundPoint = new PointGrid(pLength, pWidth, pHeight);

		for (i = 0; i < pLength; i++) {
			for (j = 0; j < pWidth; j++) {
				for (k = 0; k < pHeight; k++) {
					var index = i * pWidth * pHeight + j * pHeight + k;
					vpBits[index] &= ~ISDONE; // isdone = false
					if (vpBits[index] & INOUT) {
						if (vpBits[index] & ISBOUND) {
							totalsurfacevox++;
							boundPoint.set(i, j, k, {
								ix : i,
								iy : j,
								iz : k
							});
							vpDistance[index] = 0;
							vpBits[index] |= ISDONE;
						} else {
							totalinnervox++;
						}
					}
				}
			}
		}

		inarray = new Array();
		outarray = new Array();
		var positin = 0, positout = 0;

		for (i = 0; i < pLength; i++) {
			for (j = 0; j < pWidth; j++) {
				for (k = 0; k < pHeight; k++) {
					var index = i * pWidth * pHeight + j * pHeight + k;
					if (vpBits[index] & ISBOUND) {
						inarray.push({
							ix : i,
							iy : j,
							iz : k
						});
						positin++;
						vpBits[index] &= ~ISBOUND;
					}
				}
			}
		}

		do {
			positout = this.fastoneshell(positin, boundPoint);
			positin = 0;
			inarray = [];
			for (i = 0; i < positout; i++) {
				var index = pWidth * pHeight * outarray[i].ix + pHeight
						* outarray[i].iy + outarray[i].iz;
				vpBits[index] &= ~ISBOUND;
				if (vpDistance[index] <= 1.02 * cutRadis) {
					inarray.push({
						ix : outarray[i].ix,
						iy : outarray[i].iy,
						iz : outarray[i].iz
					});
					// inarray[positin].ix=outarray[i].ix;
					// inarray[positin].iy=outarray[i].iy;
					// inarray[positin].iz=outarray[i].iz;
					positin++;
				}
			}
		} while (positin != 0);

		var cutsf = scaleFactor - 0.5;
		if (cutsf < 0)
			cutsf = 0;
		for (i = 0; i < pLength; i++) {
			for (j = 0; j < pWidth; j++) {
				for (k = 0; k < pHeight; k++) {
					var index = i * pWidth * pHeight + j * pHeight + k;
					vpBits[index] &= ~ISBOUND;
					// ses solid
					if (vpBits[index] & INOUT) {
						if (!(vpBits[index] & ISDONE)
								|| ((vpBits[index] & ISDONE) && vpDistance[index] >= cutRadis
										- 0.50 / (0.1 + cutsf))) {
							vpBits[index] |= ISBOUND;
						}
					}
				}
			}
		}
		inarray = [];
		outarray = [];
	};

	this.fastoneshell = function(number, boundPoint) { // (int* innum,int
		// *allocout,voxel2
		// ***boundPoint, int*
		// outnum, int *elimi)
		var positout = 0;
		var tx, ty, tz;
		var dx, dy, dz;
		var square;
		if (number == 0)
			return 0;
		outarray = [];

		tnv = {
			ix : -1,
			iy : -1,
			iz : -1
		};
		for ( var i = 0; i < number; i++) {
			tx = inarray[i].ix;
			ty = inarray[i].iy;
			tz = inarray[i].iz;
			var bp = boundPoint.get(tx, ty, tz);

			for ( var j = 0; j < 6; j++) {
				tnv.ix = tx + nb[j][0];
				tnv.iy = ty + nb[j][1];
				tnv.iz = tz + nb[j][2];
				var index = tnv.ix * pWidth * pHeight + pHeight * tnv.iy
						+ tnv.iz;
				if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && !(vpBits[index] & ISDONE)) {

					boundPoint.set(tnv.ix, tnv.iy, tz + nb[j][2], bp);
					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					var square = dx * dx + dy * dy + dz * dz;
					vpDistance[index] = Math.sqrt(square);
					vpBits[index] |= ISDONE;
					vpBits[index] |= ISBOUND;

					outarray.push({
						ix : tnv.ix,
						iy : tnv.iy,
						iz : tnv.iz
					});
					positout++;
				} else if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && (vpBits[index] & ISDONE)) {

					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					square = dx * dx + dy * dy + dz * dz;
					square = Math.sqrt(square);
					if (square < vpDistance[index]) {
						boundPoint.set(tnv.ix, tnv.iy, tnv.iz, bp);

						vpDistance[index] = square;
						if (!(vpBits[index] & ISBOUND)) {
							vpBits[index] |= ISBOUND;
							outarray.push({
								ix : tnv.ix,
								iy : tnv.iy,
								iz : tnv.iz
							});
							positout++;
						}
					}
				}
			}
		}

		// console.log("part1", positout);

		for (i = 0; i < number; i++) {
			tx = inarray[i].ix;
			ty = inarray[i].iy;
			tz = inarray[i].iz;
			var bp = boundPoint.get(tx, ty, tz);

			for (j = 6; j < 18; j++) {
				tnv.ix = tx + nb[j][0];
				tnv.iy = ty + nb[j][1];
				tnv.iz = tz + nb[j][2];
				var index = tnv.ix * pWidth * pHeight + pHeight * tnv.iy
						+ tnv.iz;

				if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && !(vpBits[index] & ISDONE)) {
					boundPoint.set(tnv.ix, tnv.iy, tz + nb[j][2], bp);

					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					square = dx * dx + dy * dy + dz * dz;
					vpDistance[index] = Math.sqrt(square);
					vpBits[index] |= ISDONE;
					vpBits[index] |= ISBOUND;

					outarray.push({
						ix : tnv.ix,
						iy : tnv.iy,
						iz : tnv.iz
					});
					positout++;
				} else if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && (vpBits[index] & ISDONE)) {
					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					square = Math.sqrt(dx * dx + dy * dy + dz * dz);
					if (square < vpDistance[index]) {
						boundPoint.set(tnv.ix, tnv.iy, tnv.iz, bp);
						vpDistance[index] = square;
						if (!(vpBits[index] & ISBOUND)) {
							vpBits[index] |= ISBOUND;
							outarray.push({
								ix : tnv.ix,
								iy : tnv.iy,
								iz : tnv.iz
							});
							positout++;
						}
					}
				}
			}
		}

		// console.log("part2", positout);

		for (i = 0; i < number; i++) {
			tx = inarray[i].ix;
			ty = inarray[i].iy;
			tz = inarray[i].iz;
			var bp = boundPoint.get(tx, ty, tz);

			for (j = 18; j < 26; j++) {
				tnv.ix = tx + nb[j][0];
				tnv.iy = ty + nb[j][1];
				tnv.iz = tz + nb[j][2];
				var index = tnv.ix * pWidth * pHeight + pHeight * tnv.iy
						+ tnv.iz;

				if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && !(vpBits[index] & ISDONE)) {
					boundPoint.set(tnv.ix, tnv.iy, tz + nb[j][2], bp);

					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					square = dx * dx + dy * dy + dz * dz;
					vpDistance[index] = Math.sqrt(square);
					vpBits[index] |= ISDONE;
					vpBits[index] |= ISBOUND;

					outarray.push({
						ix : tnv.ix,
						iy : tnv.iy,
						iz : tnv.iz
					});
					positout++;
				} else if (tnv.ix < pLength && tnv.ix > -1 && tnv.iy < pWidth
						&& tnv.iy > -1 && tnv.iz < pHeight && tnv.iz > -1
						&& (vpBits[index] & INOUT) && (vpBits[index] & ISDONE)) {
					dx = tnv.ix - bp.ix;
					dy = tnv.iy - bp.iy;
					dz = tnv.iz - bp.iz;
					square = Math.sqrt(dx * dx + dy * dy + dz * dz);
					if (square < vpDistance[index]) {
						boundPoint.set(tnv.ix, tnv.iy, tnv.iz, bp);

						vpDistance[index] = square;
						if (!(vpBits[index] & ISBOUND)) {
							vpBits[index] |= ISBOUND;
							outarray.push({
								ix : tnv.ix,
								iy : tnv.iy,
								iz : tnv.iz
							});
							positout++;
						}
					}
				}
			}
		}

		// console.log("part3", positout);
		return positout;
	};

	this.marchingcubeinit = function(stype) {
		for ( var i = 0, lim = vpBits.length; i < lim; i++) {
			if (stype == 3) {// vdw
				vpBits[i] &= ~ISBOUND;
			} else if (stype == 4) { // ses
				vpBits[i] &= ~ISDONE;
				if (vpBits[i] & ISBOUND)
					vpBits[i] |= ISDONE;
				vpBits[i] &= ~ISBOUND;
			} else if (stype == 2) {// after vdw
				if ((vpBits[i] & ISBOUND) && (vpBits[i] & ISDONE))
					vpBits[i] &= ~ISBOUND;
				else if ((vpBits[i] & ISBOUND) && !(vpBits[i] & ISDONE))
					vpBits[i] |= ISDONE;
			} else if (stype == 3) { // sas
				vpBits[i] &= ~ISBOUND;
			}
		}
	};

	// return the flat index corresponding to the pos corner of
	// cube i,j,k
	var indexFromPos = function(i, j, k, pos) {
		if (pos & 1)
			k++;
		if (pos & 2)
			j++;
		if (pos & 4)
			i++;

		return ((pWidth * i) + j) * pHeight + k;
	};

	var createVertexAtPos = function(i,j,k,pos) {
		if (pos & 1)
			k++;
		if (pos & 2)
			j++;
		if (pos & 4)
			i++;

		return new Vector3(i,j,k);
	};
	
	//create (or retrieve) a vertex at the appropriate point for
	//the edge (p1,p2)
	var getVertex = function(i,j,k,code,p1,p2, vertnums) {
		var val1 = !!(code & (1<<p1));
		var val2 = !!(code & (1<<p2));
		
		//p1 if they are the same or if !val1
		var p = p1;
		if(!val1 && val2)
			p = p2;

				
		var index = indexFromPos(i,j,k,p);
		if(vertnums[index] < 0) //not created yet
		{
			vertnums[index] = verts.length;
			verts.push(createVertexAtPos(i,j,k,p));
		}
		return vertnums[index];
	};
	
	// based on code, determine what vertices are needed for cube i,j,k
	// if necessary create them (adding to verts and setting vertnums)
	// and set the appropriate vertex indices in vertList
	var setVertList = function(i, j, k, pbcode, code, vertnums, vertlist) {
		var table = MarchingCube.edgeTable;
		if (table[pbcode] == 0)
			return (0);

		/* Find the vertices where the surface intersects the cube */
		//WARNING: corner identifiers swapped 2-3 6-7
		if (table[pbcode] & 1)
			vertlist[0] = getVertex(i,j,k, code, 0, 1, vertnums);
		if (table[pbcode] & 2)
			vertlist[1] = getVertex(i,j,k, code, 1, 3, vertnums);
		if (table[pbcode] & 4)
			vertlist[2] = getVertex(i,j,k, code, 3, 2, vertnums);
		if (table[pbcode] & 8)
			vertlist[3] = getVertex(i,j,k, code, 2, 0, vertnums);
		if (table[pbcode] & 16)
			vertlist[4] = getVertex(i,j,k, code, 4, 5, vertnums);
		if (table[pbcode] & 32)
			vertlist[5] = getVertex(i,j,k, code, 5, 7, vertnums);
		if (table[pbcode] & 64)
			vertlist[6] = getVertex(i,j,k, code, 7, 6, vertnums);
		if (table[pbcode] & 128)
			vertlist[7] = getVertex(i,j,k, code, 6, 4, vertnums);
		if (table[pbcode] & 256)
			vertlist[8] = getVertex(i,j,k, code, 0, 4, vertnums);
		if (table[pbcode] & 512)
			vertlist[9] = getVertex(i,j,k, code, 1, 5, vertnums);
		if (table[pbcode] & 1024)
			vertlist[10] = getVertex(i,j,k, code, 3, 7, vertnums);
		if (table[pbcode] & 2048)
			vertlist[11] = getVertex(i,j,k, code, 2, 6, vertnums);
	};

	// this is based off the code here:
	// http://paulbourke.net/geometry/polygonise/
	// which is in turn based off of assorted public domain codes
	this.marchingcube2 = function(stype) {
		this.marchingcubeinit(stype);

		// this array keeps track of unique numbers for vertices
		// created in verts
		var vertnums = new Int32Array(pLength * pWidth * pHeight);
		for ( var i = 0; i < vertnums.length; i++) {
			vertnums[i] = -1;
		}

		verts = new Array();
		faces = new Array();

		// consider every grid cube
		var i, j, k, p, t;
		var l, w, h, trilen, vlen;
		var vertList = new Array(12);
		for (i = 0, l = pLength - 1; i < l; i++) {
			for (j = 0, w = pWidth - 1; j < w; j++) {
				for (k = 0, h = pHeight - 1; k < h; k++) {
					var code = 0;
					var pbcode = 0;
					for (p = 0; p < 8; p++) {
						var index = indexFromPos(i, j, k, p);
						var val = !!(vpBits[index] & ISDONE); 
						code |=  val << p;
						var pb = p;
						//PaulBourke does not number his corners how I would like
						switch(pb) {
						case 2: pb = 3; break;
						case 3: pb = 2; break;
						case 6: pb = 7; break;
						case 7: pb = 6; break;
						};
						pbcode |= val << pb;
					}					

					setVertList(i, j, k, pbcode, code, vertnums, vertList);
					var table = MarchingCube.triTable[pbcode];
					for (t = 0, trilen = table.length; t < trilen; t += 3) {
						faces
								.push(new Face3(vertList[table[t]],
										vertList[table[t + 1]],
										vertList[table[t + 2]]));
					}
				}
			}
		}
		//set atom ids
		for (i = 0, vlen = verts.length; i < vlen; i++) {
			verts[i].atomid = vpAtomID[verts[i].x * pWidth * pHeight + pHeight
					* verts[i].y + verts[i].z];
		}
	};

	this.marchingcube = function(stype) {
		this.marchingcubeinit(stype);
		var vertseq = new Array(pLength);
		for ( var i = 0; i < pLength; i++) {
			var a = new Array(pWidth);
			for ( var j = 0; j < pWidth; j++) {
				var b = new Array(pHeight);
				for ( var k = 0; k < pHeight; k++)
					b[k] = -1;
				a[j] = b;
			}
			vertseq[i] = a;
		}
		vertnumber = 0, facenumber = 0;
		verts = new Array();// (4 * (pHeight * pLength + pWidth * pLength +
		// pHeight * pWidth)); // CHECK: Is this enough?

		faces = new Array();// 12 * (pHeight * pLength + pWidth * pLength +
		// pHeight * pWidth)); // CHECK! 4

		var sumtype, ii, jj, kk;
		var tp = new Array(6);
		for ( var i = 0; i < 6; i++)
			tp[i] = new Array(3);

		// face1
		for (i = 0; i < 1; i++) {
			for (j = 0; j < pWidth - 1; j++) {
				for (k = 0; k < pHeight - 1; k++) {
					var vp000 = !!(vpBits[pWidth * pHeight * i + pHeight * j
							+ k] & ISDONE);
					var vp001 = !!(vpBits[pWidth * pHeight * i + pHeight * j
							+ k + 1] & ISDONE);
					var vp010 = !!(vpBits[pWidth * pHeight * i + pHeight
							* (j + 1) + k] & ISDONE);
					var vp011 = !!(vpBits[pWidth * pHeight * i + pHeight
							* (j + 1) + k + 1] & ISDONE);
					var vp100 = !!(vpBits[pWidth * pHeight * (i + 1) + pHeight
							* j + k] & ISDONE);
					var vp101 = !!(vpBits[pWidth * pHeight * (i + 1) + pHeight
							* j + k + 1] & ISDONE);
					var vp110 = !!(vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k] & ISDONE);
					var vp111 = !!(vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1] & ISDONE);

					var code = vp000 | vp001 << 1 | vp010 << 2 | vp011 << 3
							| vp100 << 4 | vp101 << 5 | vp110 << 6 | vp111 << 7;

					switch (code) {
					case 0xf: // vp000 && vp010 && vp011 && vp001
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i;
						tp[1][1] = j + 1;
						tp[1][2] = k;
						tp[2][0] = i;
						tp[2][1] = j + 1;
						tp[2][2] = k + 1;
						tp[3][0] = i;
						tp[3][1] = j;
						tp[3][2] = k + 1;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
						break;
					case 0xd:// vp000 && vp010 && vp011
					case 0xe: // vp010 && vp011 && vp001
					case 0xb: // vp011 && vp001 && vp000
					case 0x7: // vp001 && vp000 && vp010

						switch (code) {
						case 0xd: // if (vp000 && vp010 && vp011)

							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k + 1;

							break;
						case 0xe: // else if (vp010 && vp011 && vp001)

							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k + 1;

							break;
						case 0xb: // else if (vp011 && vp001 && vp000)

							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;

							break;
						case 0x7: // else if (vp001 && vp000 && vp010)

							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k;

							break;

						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
					}
				}
			}
		}
		// console.log(1);
		// face3
		for (i = 0; i < pLength - 1; i++) {
			for (j = 0; j < 1; j++) {
				for (k = 0; k < pHeight - 1; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					if (vp000 && vp100 && vp101 && vp001) {
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i + 1;
						tp[1][1] = j;
						tp[1][2] = k;
						tp[2][0] = i + 1;
						tp[2][1] = j;
						tp[2][2] = k + 1;
						tp[3][0] = i;
						tp[3][1] = j;
						tp[3][2] = k + 1;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
						facenumber++;
					} else if ((vp000 && vp100 && vp101)
							|| (vp100 && vp101 && vp001)
							|| (vp101 && vp001 && vp000)
							|| (vp001 && vp000 && vp100)) {
						if (vp000 && vp100 && vp101) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						} else if (vp100 && vp101 && vp001) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						} else if (vp101 && vp001 && vp000) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						} else if (vp001 && vp000 && vp100) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k;
						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					}
				}
			}
		}
		// console.log(3);
		// face5
		for (i = 0; i < pLength - 1; i++) {
			for (j = 0; j < pWidth - 1; j++) {
				for (k = 0; k < 1; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					if (vp000 && vp100 && vp110 && vp010) {
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i + 1;
						tp[1][1] = j;
						tp[1][2] = k;
						tp[2][0] = i + 1;
						tp[2][1] = j + 1;
						tp[2][2] = k;
						tp[3][0] = i;
						tp[3][1] = j + 1;
						tp[3][2] = k;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					} else if ((vp000 && vp100 && vp110)
							|| (vp100 && vp110 && vp010)
							|| (vp110 && vp010 && vp000)
							|| (vp010 && vp000 && vp100)) {
						if (vp000 && vp100 && vp110) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						} else if (vp100 && vp110 && vp010) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						} else if (vp110 && vp010 && vp000) {
							tp[0][0] = i + 1;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						} else if (vp010 && vp000 && vp100) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k;
						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
					}
				}
			}
		}
		// console.log(5);
		// face2
		for (i = pLength - 1; i < pLength; i++) {
			for (j = 0; j < pWidth - 1; j++) {
				for (k = 0; k < pHeight - 1; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					if (vp000 && vp010 && vp011 && vp001) {
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i;
						tp[1][1] = j + 1;
						tp[1][2] = k;
						tp[2][0] = i;
						tp[2][1] = j + 1;
						tp[2][2] = k + 1;
						tp[3][0] = i;
						tp[3][1] = j;
						tp[3][2] = k + 1;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
						facenumber++;
					} else if ((vp000 && vp010 && vp011)
							|| (vp010 && vp011 && vp001)
							|| (vp011 && vp001 && vp000)
							|| (vp001 && vp000 && vp010)) {
						if (vp000 && vp010 && vp011) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k + 1;
						} else if (vp010 && vp011 && vp001) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						} else if (vp011 && vp001 && vp000) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						} else if (vp001 && vp000 && vp010) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					}

				}
			}
		}
		// console.log(2);
		// face4
		for (i = 0; i < pLength - 1; i++) {
			for (j = pWidth - 1; j < pWidth; j++) {
				for (k = 0; k < pHeight - 1; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					if (vp000 && vp100 && vp101 && vp001) {
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i + 1;
						tp[1][1] = j;
						tp[1][2] = k;
						tp[2][0] = i + 1;
						tp[2][1] = j;
						tp[2][2] = k + 1;
						tp[3][0] = i;
						tp[3][1] = j;
						tp[3][2] = k + 1;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					} else if ((vp000 && vp100 && vp101)
							|| (vp100 && vp101 && vp001)
							|| (vp101 && vp001 && vp000)
							|| (vp001 && vp000 && vp100)) {
						if (vp000 && vp100 && vp101) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						} else if (vp100 && vp101 && vp001) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						} else if (vp101 && vp001 && vp000) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						} else if (vp001 && vp000 && vp100) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k;
						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
						facenumber++;
					}

				}
			}
		}
		// console.log(4);
		// face6
		for (i = 0; i < pLength - 1; i++) {
			for (j = 0; j < pWidth - 1; j++) {
				for (k = pHeight - 1; k < pHeight; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					if (vp000 && vp100 && vp110 && vp010) {
						tp[0][0] = i;
						tp[0][1] = j;
						tp[0][2] = k;
						tp[1][0] = i + 1;
						tp[1][1] = j;
						tp[1][2] = k;
						tp[2][0] = i + 1;
						tp[2][1] = j + 1;
						tp[2][2] = k;
						tp[3][0] = i;
						tp[3][1] = j + 1;
						tp[3][2] = k;
						for (ii = 0; ii < 4; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
								vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
						facenumber++;
					} else if ((vp000 && vp100 && vp110)
							|| (vp100 && vp110 && vp010)
							|| (vp110 && vp010 && vp000)
							|| (vp010 && vp000 && vp100)) {
						if (vp000 && vp100 && vp110) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						} else if (vp100 && vp110 && vp010) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						} else if (vp110 && vp010 && vp000) {
							tp[0][0] = i + 1;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						} else if (vp010 && vp000 && vp100) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k;
						}
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					}
				}
			}
		}
		// console.log(6);
		for (i = 0; i < pLength - 1; i++) {
			// console.log(i);
			for (j = 0; j < pWidth - 1; j++) {
				for (k = 0; k < pHeight - 1; k++) {
					var vp000 = vpBits[pWidth * pHeight * i + pHeight * j + k]
							& ISDONE;
					var vp001 = vpBits[pWidth * pHeight * i + pHeight * j + k
							+ 1]
							& ISDONE;
					var vp010 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k]
							& ISDONE;
					var vp011 = vpBits[pWidth * pHeight * i + pHeight * (j + 1)
							+ k + 1]
							& ISDONE;
					var vp100 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k]
							& ISDONE;
					var vp101 = vpBits[pWidth * pHeight * (i + 1) + pHeight * j
							+ k + 1]
							& ISDONE;
					var vp110 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k]
							& ISDONE;
					var vp111 = vpBits[pWidth * pHeight * (i + 1) + pHeight
							* (j + 1) + k + 1]
							& ISDONE;

					var sumtype = 0;
					for (ii = 0; ii < 2; ii++) {
						for (jj = 0; jj < 2; jj++) {
							for (kk = 0; kk < 2; kk++) {
								if (vpBits[pWidth * pHeight * (i + ii)
										+ pHeight * (j + jj) + k + kk]
										& ISDONE)
									sumtype++;
							}
						}
					}

					if (sumtype == 3) {
						if ((vp000 && vp100 && vp110)
								|| (vp000 && vp010 && vp110)
								|| (vp010 && vp100 && vp110)
								|| (vp000 && vp010 && vp100)
								|| (vp001 && vp101 && vp111)
								|| (vp001 && vp011 && vp111)
								|| (vp011 && vp101 && vp111)
								|| (vp001 && vp011 && vp101)
								|| (vp000 && vp100 && vp101)
								|| (vp100 && vp101 && vp001)
								|| (vp000 && vp101 && vp001)
								|| (vp000 && vp100 && vp001)
								|| (vp110 && vp100 && vp111)
								|| (vp110 && vp101 && vp111)
								|| (vp100 && vp101 && vp111)
								|| (vp110 && vp100 && vp101)
								|| (vp110 && vp010 && vp011)
								|| (vp010 && vp011 && vp111)
								|| (vp110 && vp011 && vp111)
								|| (vp110 && vp010 && vp111)
								|| (vp000 && vp010 && vp001)
								|| (vp000 && vp001 && vp011)
								|| (vp001 && vp010 && vp011)
								|| (vp000 && vp010 && vp011)) {
							if (vp000 && vp100 && vp110) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 11
							else if (vp000 && vp010 && vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 12
							else if (vp010 && vp100 && vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 13
							else if (vp000 && vp010 && vp100) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 14
							else if (vp001 && vp101 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 21
							else if (vp001 && vp011 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 22
							else if (vp011 && vp101 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 23
							else if (vp001 && vp011 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 24
							else if (vp000 && vp100 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 31
							else if (vp100 && vp101 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 32
							else if (vp000 && vp101 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 33
							else if (vp000 && vp100 && vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 34
							else if (vp110 && vp100 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 41
							else if (vp110 && vp101 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 42
							else if (vp100 && vp101 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 43
							else if (vp110 && vp100 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 44
							else if (vp110 && vp010 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 51
							else if (vp010 && vp011 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 52
							else if (vp110 && vp011 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 53
							else if (vp110 && vp010 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 54
							else if (vp000 && vp010 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 61
							else if (vp000 && vp001 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 62
							else if (vp001 && vp010 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 63
							else if (vp000 && vp010 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 64
							for (ii = 0; ii < 3; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
						}// no5 24
					}// total3
					else if (sumtype == 4) { // CHECK
						if ((vp000 && vp100 && vp110 && vp010)
								|| (vp001 && vp101 && vp111 && vp011)
								|| (vp000 && vp100 && vp101 && vp001)
								|| (vp110 && vp100 && vp101 && vp111)
								|| (vp110 && vp010 && vp011 && vp111)
								|| (vp000 && vp010 && vp001 && vp011)) {
							if (vp000 && vp100 && vp110 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;

							} else if (vp001 && vp101 && vp111 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							} else if (vp000 && vp100 && vp101 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							} else if (vp110 && vp100 && vp101 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							} else if (vp110 && vp010 && vp011 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							} else if (vp000 && vp010 && vp001 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no.8 6

						else if ((vp000 && vp100 && vp110 && vp011)// 11
								|| (vp000 && vp010 && vp110 && vp101)// 12
								|| (vp010 && vp100 && vp110 && vp001)// 13
								|| (vp000 && vp010 && vp100 && vp111)// 14
								|| (vp001 && vp101 && vp111 && vp010)// 21
								|| (vp001 && vp011 && vp111 && vp100)// 22
								|| (vp011 && vp101 && vp111 && vp000)// 23
								|| (vp001 && vp011 && vp101 && vp110)// 24
								|| (vp000 && vp100 && vp101 && vp011)// 31
								|| (vp100 && vp101 && vp001 && vp010)// 32
								|| (vp000 && vp101 && vp001 && vp110)// 33
								|| (vp000 && vp100 && vp001 && vp111)// 34
								|| (vp110 && vp100 && vp111 && vp001)// 41
								|| (vp110 && vp101 && vp111 && vp000)// 42
								|| (vp100 && vp101 && vp111 && vp010)// 43
								|| (vp110 && vp100 && vp101 && vp011)// 44
								|| (vp110 && vp010 && vp011 && vp101)// 51
								|| (vp010 && vp011 && vp111 && vp100)// 52
								|| (vp110 && vp011 && vp111 && vp000)// 53
								|| (vp110 && vp010 && vp111 && vp001)// 54
								|| (vp000 && vp010 && vp001 && vp111)// 61
								|| (vp000 && vp001 && vp011 && vp110)// 62
								|| (vp001 && vp010 && vp011 && vp100)// 63
								|| (vp000 && vp010 && vp011 && vp101)) {
							if (vp000 && vp100 && vp110 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 11
							else if (vp000 && vp010 && vp110 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 12
							else if (vp010 && vp100 && vp110 && vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 13
							else if (vp000 && vp010 && vp100 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 14
							else if (vp001 && vp101 && vp111 && vp010) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 21
							else if (vp001 && vp011 && vp111 && vp100) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 22
							else if (vp011 && vp101 && vp111 && vp000) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 23
							else if (vp001 && vp011 && vp101 && vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 24
							else if (vp000 && vp100 && vp101 && vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 31
							else if (vp100 && vp101 && vp001 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 32
							else if (vp000 && vp101 && vp001 && vp110) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 33
							else if (vp000 && vp100 && vp001 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 34
							else if (vp110 && vp100 && vp111 && vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 41
							else if (vp110 && vp101 && vp111 && vp000) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 42
							else if (vp100 && vp101 && vp111 && vp010) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 43
							else if (vp110 && vp100 && vp101 && vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 44
							else if (vp110 && vp010 && vp011 && vp101) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 51
							else if (vp010 && vp011 && vp111 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 52
							else if (vp110 && vp011 && vp111 && vp000) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 53
							else if (vp110 && vp010 && vp111 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 54
							else if (vp000 && vp010 && vp001 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 61
							else if (vp000 && vp001 && vp011 && vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 62
							else if (vp001 && vp010 && vp011 && vp100) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
							}// 63
							else if (vp000 && vp010 && vp011 && vp101) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
							}// 64
							for (ii = 0; ii < 3; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;

						}// no12 24
						else if ((vp000 && vp011 && vp110 && vp010)
								|| (vp000 && vp100 && vp110 && vp101)
								|| (vp000 && vp001 && vp100 && vp010)
								|| (vp010 && vp100 && vp110 && vp111)
								|| (vp001 && vp011 && vp111 && vp010)
								|| (vp001 && vp100 && vp111 && vp101)
								|| (vp000 && vp001 && vp101 && vp011)
								|| (vp011 && vp101 && vp110 && vp111)) {
							if (vp010 && vp011 && vp000 && vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 1
							else if (vp100 && vp101 && vp110 && vp000) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 2
							else if (vp000 && vp001 && vp100 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 3
							else if (vp110 && vp111 && vp010 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 4
							else if (vp010 && vp011 && vp111 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							}// 5
							else if (vp100 && vp101 && vp111 && vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							}// 6
							else if (vp000 && vp001 && vp101 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							}// 7
							else if (vp011 && vp101 && vp110 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							}// 8
							for (ii = 0; ii < 3; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
						}// no.9 8
						else if ((vp000 && vp100 && vp110 && vp001)
								|| (vp010 && vp100 && vp110 && vp101)
								|| (vp010 && vp000 && vp110 && vp111)
								|| (vp010 && vp000 && vp100 && vp011)
								|| (vp011 && vp001 && vp101 && vp100)
								|| (vp111 && vp001 && vp101 && vp110)
								|| (vp111 && vp011 && vp101 && vp010)
								|| (vp111 && vp011 && vp001 && vp000)
								|| (vp110 && vp011 && vp001 && vp010)
								|| (vp101 && vp000 && vp001 && vp010)
								|| (vp101 && vp000 && vp111 && vp100)
								|| (vp011 && vp110 && vp111 && vp100)) {
							if (vp000 && vp100 && vp110 && vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 1
							else if (vp010 && vp100 && vp110 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 2
							else if (vp010 && vp000 && vp110 && vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 3
							else if (vp010 && vp000 && vp100 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 4
							else if (vp011 && vp001 && vp101 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 5
							else if (vp111 && vp001 && vp101 && vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 6
							else if (vp111 && vp011 && vp101 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 7
							else if (vp111 && vp011 && vp001 && vp000) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 8
							else if (vp110 && vp011 && vp001 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 9
							else if (vp101 && vp000 && vp001 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 10
							else if (vp101 && vp000 && vp111 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 11
							else if (vp011 && vp110 && vp111 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 12
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no.11 12
						else if ((vp000 && vp100 && vp010 && vp101)
								|| (vp000 && vp100 && vp110 && vp111)
								|| (vp010 && vp100 && vp110 && vp011)
								|| (vp010 && vp000 && vp110 && vp001)
								|| (vp111 && vp001 && vp101 && vp000)
								|| (vp111 && vp011 && vp101 && vp100)
								|| (vp111 && vp011 && vp001 && vp110)
								|| (vp101 && vp011 && vp001 && vp010)
								|| (vp111 && vp011 && vp000 && vp010)
								|| (vp100 && vp000 && vp001 && vp011)
								|| (vp101 && vp001 && vp110 && vp100)
								|| (vp010 && vp110 && vp111 && vp101)) {
							if (vp000 && vp100 && vp010 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 1
							else if (vp000 && vp100 && vp110 && vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 2
							else if (vp010 && vp100 && vp110 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 3
							else if (vp010 && vp000 && vp110 && vp001) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 4
							else if (vp111 && vp001 && vp101 && vp000) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 5
							else if (vp111 && vp011 && vp101 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 6
							else if (vp111 && vp011 && vp001 && vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 7
							else if (vp101 && vp011 && vp001 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 8
							else if (vp111 && vp011 && vp000 && vp010) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 9
							else if (vp100 && vp000 && vp001 && vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 10
							else if (vp101 && vp001 && vp110 && vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 11
							else if (vp010 && vp110 && vp111 && vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 12
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no.14 12
					}// total4
					else if (sumtype == 5) {
						if ((!vp100 && !vp001 && !vp111)
								|| (!vp010 && !vp001 && !vp111)
								|| (!vp110 && !vp101 && !vp011)
								|| (!vp000 && !vp101 && !vp011)
								|| (!vp101 && !vp000 && !vp110)
								|| (!vp011 && !vp000 && !vp110)
								|| (!vp111 && !vp100 && !vp010)
								|| (!vp001 && !vp100 && !vp010)) {
							if (!vp100 && !vp001 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 1
							else if (!vp010 && !vp001 && !vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 2
							else if (!vp110 && !vp101 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
							}// 3
							else if (!vp000 && !vp101 && !vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
							}// 4
							else if (!vp101 && !vp000 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							}// 5
							else if (!vp011 && !vp000 && !vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							}// 6
							else if (!vp111 && !vp100 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							}// 7
							else if (!vp001 && !vp100 && !vp010) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
							}// 8
							for (ii = 0; ii < 3; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
						}// no.7 8
						else if ((!vp000 && !vp100 && !vp110)
								|| (!vp000 && !vp010 && !vp110)
								|| (!vp010 && !vp100 && !vp110)
								|| (!vp000 && !vp010 && !vp100)
								|| (!vp001 && !vp101 && !vp111)
								|| (!vp001 && !vp011 && !vp111)
								|| (!vp011 && !vp101 && !vp111)
								|| (!vp001 && !vp011 && !vp101)
								|| (!vp000 && !vp100 && !vp101)
								|| (!vp100 && !vp101 && !vp001)
								|| (!vp000 && !vp101 && !vp001)
								|| (!vp000 && !vp100 && !vp001)
								|| (!vp110 && !vp100 && !vp111)
								|| (!vp110 && !vp101 && !vp111)
								|| (!vp100 && !vp101 && !vp111)
								|| (!vp110 && !vp100 && !vp101)
								|| (!vp110 && !vp010 && !vp011)
								|| (!vp010 && !vp011 && !vp111)
								|| (!vp110 && !vp011 && !vp111)
								|| (!vp110 && !vp010 && !vp111)
								|| (!vp000 && !vp010 && !vp001)
								|| (!vp000 && !vp001 && !vp011)
								|| (!vp001 && !vp010 && !vp011)
								|| (!vp000 && !vp010 && !vp011)) {
							if (!vp000 && !vp100 && !vp110) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 11
							else if (!vp000 && !vp010 && !vp110) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 12
							else if (!vp010 && !vp100 && !vp110) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 13
							else if (!vp000 && !vp010 && !vp100) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 14
							else if (!vp001 && !vp101 && !vp111) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 21
							else if (!vp001 && !vp011 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 22
							else if (!vp011 && !vp101 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 23
							else if (!vp001 && !vp011 && !vp101) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 24
							else if (!vp000 && !vp100 && !vp101) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 31
							else if (!vp100 && !vp101 && !vp001) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 32
							else if (!vp000 && !vp101 && !vp001) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 33
							else if (!vp000 && !vp100 && !vp001) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 34
							else if (!vp110 && !vp100 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 41
							else if (!vp110 && !vp101 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 42
							else if (!vp100 && !vp101 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 43
							else if (!vp110 && !vp100 && !vp101) {
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 44
							else if (!vp110 && !vp010 && !vp011) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 51
							else if (!vp010 && !vp011 && !vp111) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 52
							else if (!vp110 && !vp011 && !vp111) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 53
							else if (!vp110 && !vp010 && !vp111) {
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 54
							else if (!vp000 && !vp010 && !vp001) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 61
							else if (!vp000 && !vp001 && !vp011) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 62
							else if (!vp001 && !vp010 && !vp011) {
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 63
							else if (!vp000 && !vp010 && !vp011) {
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 64
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no5 24
						else if ((!vp000 && !vp100 && !vp111)// 1
								|| (!vp010 && !vp110 && !vp001)// 2
								|| (!vp011 && !vp111 && !vp100)// 3
								|| (!vp001 && !vp101 && !vp110)// 4
								|| (!vp000 && !vp010 && !vp111)// 5
								|| (!vp101 && !vp111 && !vp010)// 6
								|| (!vp100 && !vp110 && !vp011)// 7
								|| (!vp001 && !vp011 && !vp110)// 8
								|| (!vp000 && !vp001 && !vp111)// 9
								|| (!vp110 && !vp111 && !vp000)// 10
								|| (!vp100 && !vp101 && !vp011)// 11
								|| (!vp010 && !vp011 && !vp101)) {
							if (!vp000 && !vp100 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 1
							else if (!vp010 && !vp110 && !vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 2
							else if (!vp011 && !vp111 && !vp100) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 3
							else if (!vp001 && !vp101 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 4
							else if (!vp000 && !vp010 && !vp111) {
								// tp[0][0]=i;tp[0][1]=j;tp[0][2]=k+1;
								// tp[1][0]=i+1;tp[1][1]=j;tp[1][2]=k;
								// tp[2][0]=i+1;tp[2][1]=j+1;tp[2][2]=k;
								// tp[3][0]=i;tp[3][1]=j+1;tp[3][2]=k+1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 5
							else if (!vp101 && !vp111 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 6
							else if (!vp100 && !vp110 && !vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 7
							else if (!vp001 && !vp011 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 8
							else if (!vp000 && !vp001 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 9
							else if (!vp110 && !vp111 && !vp000) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 10
							else if (!vp100 && !vp101 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 11
							else if (!vp010 && !vp011 && !vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 12
							for (ii = 0; ii < 5; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[4][0]][tp[4][1]][tp[4][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;

						}// no.6 12-1
						else if ((!vp000 && !vp100 && !vp011)// 1
								|| (!vp010 && !vp110 && !vp101)// 2
								|| (!vp011 && !vp111 && !vp000)// 3
								|| (!vp001 && !vp101 && !vp010)// 4
								|| (!vp000 && !vp010 && !vp101)// 5
								|| (!vp101 && !vp111 && !vp000)// 6
								|| (!vp100 && !vp110 && !vp001)// 7
								|| (!vp001 && !vp011 && !vp100)// 8
								|| (!vp000 && !vp001 && !vp110)// 9
								|| (!vp110 && !vp111 && !vp001)// 10
								|| (!vp100 && !vp101 && !vp010)// 11
								|| (!vp010 && !vp011 && !vp100)) {
							if (!vp000 && !vp100 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 1
							else if (!vp010 && !vp110 && !vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 2
							else if (!vp011 && !vp111 && !vp000) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 3
							else if (!vp001 && !vp101 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 4
							else if (!vp000 && !vp010 && !vp101) {
								// tp[0][0]=i;tp[0][1]=j;tp[0][2]=k+1;
								// tp[1][0]=i+1;tp[1][1]=j;tp[1][2]=k;
								// tp[2][0]=i+1;tp[2][1]=j+1;tp[2][2]=k;
								// tp[3][0]=i;tp[3][1]=j+1;tp[3][2]=k+1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 5
							else if (!vp101 && !vp111 && !vp000) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 6
							else if (!vp100 && !vp110 && !vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 7
							else if (!vp001 && !vp011 && !vp100) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k;
							}// 8
							else if (!vp000 && !vp001 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 9
							else if (!vp110 && !vp111 && !vp001) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k;
							}// 10
							else if (!vp100 && !vp101 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k + 1;
							}// 11
							else if (!vp010 && !vp011 && !vp100) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k + 1;
							}// 12
							for (ii = 0; ii < 5; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[4][0]][tp[4][1]][tp[4][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]]));
							facenumber++;
						}// no.6 12-2

					}// total5

					else if (sumtype == 6) {
						if ((!vp000 && !vp100) || (!vp010 && !vp110)
								|| (!vp011 && !vp111) || (!vp001 && !vp101)
								|| (!vp000 && !vp010) || (!vp101 && !vp111)
								|| (!vp100 && !vp110) || (!vp001 && !vp011)
								|| (!vp000 && !vp001) || (!vp110 && !vp111)
								|| (!vp100 && !vp101) || (!vp010 && !vp011)) {
							if (!vp000 && !vp100) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
							}// 1
							else if (!vp010 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
							}// 2
							else if (!vp011 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 3
							else if (!vp001 && !vp101) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 4
							else if (!vp000 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 5
							else if (!vp101 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
							}// 6
							else if (!vp100 && !vp110) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 7
							else if (!vp001 && !vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
							}// 8
							else if (!vp000 && !vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 9
							else if (!vp110 && !vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
							}// 10
							else if (!vp100 && !vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 11
							else if (!vp010 && !vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
							}// 12
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no.2 12

						else if ((!vp000 && !vp111) || (!vp100 && !vp011)
								|| (!vp010 && !vp101) || (!vp110 && !vp001)) {
							if (!vp000 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j + 1;
								tp[4][2] = k;
								tp[5][0] = i + 1;
								tp[5][1] = j;
								tp[5][2] = k;
							}// 1
							else if (!vp100 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
								tp[4][0] = i;
								tp[4][1] = j;
								tp[4][2] = k;
								tp[5][0] = i + 1;
								tp[5][1] = j + 1;
								tp[5][2] = k;
							}// 2
							else if (!vp010 && !vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j + 1;
								tp[4][2] = k;
								tp[5][0] = i;
								tp[5][1] = j;
								tp[5][2] = k;
							}// 3
							else if (!vp110 && !vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
								tp[4][0] = i + 1;
								tp[4][1] = j;
								tp[4][2] = k;
								tp[5][0] = i;
								tp[5][1] = j + 1;
								tp[5][2] = k;
							}// 4
							for (ii = 0; ii < 6; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]],
									vertseq[tp[4][0]][tp[4][1]][tp[4][2]],
									vertseq[tp[5][0]][tp[5][1]][tp[5][2]]));
							facenumber++;
						}// no.4 4

						else if ((!vp000 && !vp101) || (!vp100 && !vp001)
								|| (!vp100 && !vp111) || (!vp110 && !vp101)
								|| (!vp110 && !vp011) || (!vp010 && !vp111)
								|| (!vp010 && !vp001) || (!vp000 && !vp011)
								|| (!vp001 && !vp111) || (!vp101 && !vp011)
								|| (!vp000 && !vp110) || (!vp100 && !vp010)) {
							if (!vp000 && !vp101) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 1
							else if (!vp100 && !vp001) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 2
							else if (!vp100 && !vp111) {
								tp[0][0] = i + 1;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k + 1;
							}// 3
							else if (!vp110 && !vp101) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 4
							else if (!vp110 && !vp011) {
								tp[0][0] = i + 1;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 5
							else if (!vp010 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 6
							else if (!vp010 && !vp001) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 7
							else if (!vp000 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[2][0] = i;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k;
							}// 8
							else if (!vp001 && !vp111) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k + 1;
								tp[1][0] = i;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[3][0] = i + 1;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 9
							else if (!vp101 && !vp011) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k + 1;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k + 1;
								tp[1][0] = i + 1;
								tp[1][1] = j;
								tp[1][2] = k;
								tp[3][0] = i;
								tp[3][1] = j + 1;
								tp[3][2] = k;
							}// 10
							else if (!vp000 && !vp110) {
								tp[0][0] = i;
								tp[0][1] = j + 1;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j;
								tp[2][2] = k;
								tp[1][0] = i + 1;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[3][0] = i;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 11
							else if (!vp100 && !vp010) {
								tp[0][0] = i;
								tp[0][1] = j;
								tp[0][2] = k;
								tp[2][0] = i + 1;
								tp[2][1] = j + 1;
								tp[2][2] = k;
								tp[1][0] = i;
								tp[1][1] = j + 1;
								tp[1][2] = k + 1;
								tp[3][0] = i + 1;
								tp[3][1] = j;
								tp[3][2] = k + 1;
							}// 12
							for (ii = 0; ii < 4; ii++) {
								if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
									vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
									verts.push(new Vector3(tp[ii][0],
											tp[ii][1], tp[ii][2]));
									vertnumber++;
								}
							}
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
							facenumber++;
							faces.push(new Face3(
									vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
									vertseq[tp[2][0]][tp[2][1]][tp[2][2]],
									vertseq[tp[3][0]][tp[3][1]][tp[3][2]]));
							facenumber++;
						}// no.3 12

					}// total6

					else if (sumtype == 7) {
						if (!vp000) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						}// 1
						else if (!vp100) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i + 1;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k + 1;
						}// 2
						else if (!vp110) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k;
							tp[2][0] = i + 1;
							tp[2][1] = j + 1;
							tp[2][2] = k + 1;
						}// 3
						else if (!vp010) {
							tp[0][0] = i + 1;
							tp[0][1] = j + 1;
							tp[0][2] = k;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k + 1;
						}// 4
						else if (!vp001) {
							tp[0][0] = i + 1;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j + 1;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j;
							tp[2][2] = k;
						}// 5
						else if (!vp101) {
							tp[0][0] = i + 1;
							tp[0][1] = j + 1;
							tp[0][2] = k + 1;
							tp[1][0] = i;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i + 1;
							tp[2][1] = j;
							tp[2][2] = k;
						}// 6
						else if (!vp111) {
							tp[0][0] = i;
							tp[0][1] = j + 1;
							tp[0][2] = k + 1;
							tp[1][0] = i + 1;
							tp[1][1] = j;
							tp[1][2] = k + 1;
							tp[2][0] = i + 1;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						}// 7
						else if (!vp011) {
							tp[0][0] = i;
							tp[0][1] = j;
							tp[0][2] = k + 1;
							tp[1][0] = i + 1;
							tp[1][1] = j + 1;
							tp[1][2] = k + 1;
							tp[2][0] = i;
							tp[2][1] = j + 1;
							tp[2][2] = k;
						}// 8
						for (ii = 0; ii < 3; ii++) {
							if (vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] == -1) {
								vertseq[tp[ii][0]][tp[ii][1]][tp[ii][2]] = vertnumber;
								verts.push(new Vector3(tp[ii][0], tp[ii][1],
										tp[ii][2]));
								vertnumber++;
							}
						}
						faces.push(new Face3(
								vertseq[tp[0][0]][tp[0][1]][tp[0][2]],
								vertseq[tp[1][0]][tp[1][1]][tp[1][2]],
								vertseq[tp[2][0]][tp[2][1]][tp[2][2]]));
						facenumber++;
					}// total7

				}// every ijk
			}// j
		}// i
		this.faces = faces;
		this.verts = verts;
		for (i = 0; i < vertnumber; i++) {
			verts[i].atomid = vpAtomID[verts[i].x * pWidth * pHeight + pHeight
					* verts[i].y + verts[i].z];
		}
	};

});
