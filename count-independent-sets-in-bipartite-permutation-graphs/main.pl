#!/usr/bin/perl
#
# Count independet sets(IS), maximal independent sets(MIS), and independent perfect dominating sets(IPDS) in a bipartite permutation graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=6;       # |X|
$m=7;       # |Y|     

@L1=@L2=();   # for permutaton diagram
%L1x=%L2x=(); # the inverse functions of L1 and L2
@adj=();      # the adjacent matrix 
@delta_x=@delta_y=();  # see paper

while ( $test++ < 20 ){ # test 20 random instances	  	  
	print "\n== test $test: ";
	&new_g();
	&print_g(); 

	print "our proposed algorithm	 : ";	
	&compute_delta();
	($IS1)=&compute_IS(); 
	($MIS1, $IPDS1)=&compute_MIS_IPDS(); 
	print "|IS|=$IS1 |MIS|=$MIS1 |IPDS|=$IPDS1\n";

	print "the brute-force algorithm: ";	
	($IS2,$MIS2,$IPDS2)=&brute_force();
	print "|IS|=$IS2 |MIS|=$MIS2 |IPDS|=$IPDS2\n";
	
	if ($IS1!=$IS2 || $MIS1!=$MIS2 || $IPDS1!=$IPDS2){
		print "An error occured. Stop!\n";
		exit;
	}  
}
print "\n Tests completed successfully.\n";


sub print_g {
	print " ==> bipartite permutation |X|=$n |Y|=$m ==> \n";
	print " Line L1 ==> ";
	for ($p=1 ; $p < scalar(@L1) ; $p++){
		($xy,$index)=split("#",$L1[$p]);
		print "$xy($index)  ";
	}	
	print "\n";
	print " Line L2 ==> ";
	for ($p=1 ; $p < scalar(@L2) ; $p++){
		($xy,$index)=split("#",$L2[$p]);
		print "$xy($index)  ";
	}	
	print "\n";
}


#-------------- compute delta -----------
# time_complexity: O(|V|) where |V|=n+m
sub compute_delta { 
	@delta_x=(); # delta_x[i] store the set of 'y' vertices in G(xi) but not in G(xi+1)
	@delta_y=(); # delta_y[i] store the set of 'x' vertices in G(yi) but not in G(yi+1)

	for ($i=0 ; $i <= $n ; $i++){ # note: add one dummy vertex x0 
		$delta_x[$i]= Set::Scalar->new; # initial values
	}	
	for ($j=0 ; $j <= $m ; $j++){ # note: add one dummy vertex y0 
		$delta_y[$j]= Set::Scalar->new; # initial values
	}	
	#--- compute delta_x ---
	#scan all points on L1
	for ($i=0,$j=0, $p=1 ; $p < scalar(@L1)-1 ; $p++){  #does not include the dummy vertex of xn-1
		($xy,$k)=split("#",$L1[$p]);
		if ($xy eq 'x'){ # xk point
			$delta_y[$j]->insert($k) if (!$adj[$k][$j+1]);	  	  
			$i=$k;	  
		}else{  # yk point
			$delta_x[$i]->insert($k) if (!$adj[$i+1][$k]);
			$j=$k;
		}
	}  
	#scan all points on L2
	for ($i=0, $j=0, $p=1 ; $p < scalar(@L2)-1 ; $p++){ #does not include the dummy vertex of xn-1
		($xy,$k)=split("#",$L2[$p]);
		if ($xy eq 'x'){ # xk point
			$delta_y[$j]->insert($k) if (!$adj[$k][$j+1]);
			$i=$k;	  	  
		}else{  # yk point
			$delta_x[$i]->insert($k) if (!$adj[$i+1][$k]);
			$j=$k;
		}
	}
}

#-------------- compute IS -------------
# time_complexity: O(|V|) where |V|=n+m
sub compute_IS {
	@ISx=@ISy=();     
	for ($p=1 ; $p < scalar(@L1) ; $p++){  # note: include the dummy vertex 'x' on the rightmost side
		($xy,$i)=split("#",$L1[$p]);
		if ($xy eq 'x'){ # p is the endpoint of xi on L1
			if ($i==1){
				$ISx[$i]=1;
			}else{	
				$ISx[$i]=2*$ISx[$i-1];
			}	
			foreach $y ($delta_x[$i-1]->elements){
				$ISx[$i]+=$ISy[$y];
			}
		}else{  # xy eq 'y' and # p is the endpoint of yi on L1
			if ($i==1){
				$ISy[$i]=1;
			}else{	
				$ISy[$i]=2*$ISy[$i-1];
			}	
			foreach $x ($delta_y[$i-1]->elements){
				$ISy[$i]+=$ISx[$x];
			}	
		}	
	}
	return($ISx[$n+1]);  #return the #IS of dummy vertex 'x'
}

#-------------- compute MIS and IPDS ----------
# time_complexity: O(|V|) where |V|=n+m
sub compute_MIS_IPDS { 
	@MISx=@MISy=@IPDSx=@IPDSy=();
	$MISx[0]=$MISy[0]=$IPDSx[0]=$IPDSy[0]=1;  # boundary conditions
	for ($p=1 ; $p < scalar(@L1) ; $p++){ #note: include the dummy vertex 'x' on the rightmost side
		($xy,$i)=split("#",$L1[$p]);	
		$ix=$i-1;
		if ($xy eq 'x'){ # p is the endpoint of xi on L1
			$IPDSx[$i]=0;
			if ($delta_x[$i-1]->is_empty){ # case 1: imply xi-1 is isolated in G(xi)
				$MISx[$i]=$MISx[$i-1];  
				$IPDSx[$i]=$IPDSx[$i-1] if ($L1x{"x$ix"}==$L2x{"x$ix"}); # if xi-1 is isolated in G
			}else{ # $delta_x[$i-1] is not empty
				$max_y=0;
				foreach $y ($delta_x[$i-1]->elements){ #find the max_y in delta_x[i-1]
					$max_y=$y if ($y > $max_y);
				}
				$MISx[$i]=$MISy[$max_y];  # case 2: delta_x[i-1] is not empty and (xi-1, max_y) are not adjacent
				$IPDSx[$i]=$IPDSy[$max_y];
				if ($adj[$i-1][$max_y]){  # case 3: delta_x[i-1] is not empty (xi-1, max_y) are adjacent
					$MISx[$i]+=$MISx[$i-1] ; 		  
					$IPDSx[$i]=$IPDSy[$max_y]; 
					$IPDSx[$i]+=$IPDSx[$i-1] if (!($adj[$i-1][$max_y+1] && $adj[$i][$max_y+1])); 
				}
			}
		}else{ # p is the endpoint of yi on L1
			$IPDSy[$i]=0;
			if ($delta_y[$i-1]->is_empty){
				$MISy[$i]=$MISy[$i-1];  
				$IPDSy[$i]=$IPDSy[$i-1] if ($L1x{"y$ix"}==$L2x{"y$ix"});
			}else{ # $delta_x[$i-1] is not empty
				$max_x=0;
				foreach $x ($delta_y[$i-1]->elements){
					$max_x=$x if ($x > $max_x);
				}
				$MISy[$i]=$MISx[$max_x];
				$IPDSy[$i]=$IPDSx[$max_x];
				if ($adj[$max_x][$i-1]){		  
					$MISy[$i]+=$MISy[$i-1] ; 		  
					$IPDSy[$i]=$IPDSx[$max_x]; 
					$IPDSy[$i]+=$IPDSy[$i-1] if (!($adj[$max_x+1][$i-1] && $adj[$max_x+1][$i])); 
				}
			}
		}
	}
	return($MISx[$n+1],$IPDSx[$n+1]);#  return #MIS and #IPDS of the dummy vertex 'x' 
}

sub new_g {   #create the permutation diagram for a random bipartite permutation graph
	@px1=@px2=@py1=@py2=();  
	@adj=();  
	@L1=@L2=();  
	%L1x=%L2x=(); 
	# generate two endpoints on L1 and L2 for each x in X
	for ($a=1; $a <=$n ; $a++){  
		$x=$px1[$a]=rand($n+$m);  # set endpoints p1 and p2 of "x" on L1  
		# search the lower bound and upper bound for x
		$p1_lowbound=$p2_lowbound=1; 
		$p1_upbound=$p2_upbound=$n+$m;	 
		for ($j=1 ; $j < $a ; $j++){
			if ($px1[$j] < $x && $px1[$j] > $p1_lowbound){
				$p1_lowbound=$px1[$j];
				$p2_lowbound=$px2[$j];
			}
			if ($px1[$j] > $x && $px1[$j] < $p1_upbound){
				$p1_upbound=$px1[$j];
				$p2_upbound=$px2[$j];
			}
		}
		# set endpoints p1 and p2 of "x" on L2  
		$px2[$a]=$p2_lowbound+rand($p2_upbound-$p2_lowbound);  	 
	}

	# generate two endpoints on L1 and L2 for each y in Y
	for ($b=1; $b <=$m ; $b++){  
		$x=$py1[$b]=rand($n+$m);  # set endpoints p1 and p2 of "y" on L1  
		# search the lowber ound and upper bound of vertex y
		$p1_lowbound=$p2_lowbound=1; 
		$p1_upbound=$p2_upbound=$n+$m;	 
		for ($j=1 ; $j < $b ; $j++){
			if ($py1[$j] < $x && $py1[$j] > $p1_lowbound){
				$p1_lowbound=$py1[$j];
				$p2_lowbound=$py2[$j];
			}
			if ($py1[$j] > $x && $py1[$j] < $p1_upbound){
				$p1_upbound=$py1[$j];
				$p2_upbound=$py2[$j];
			}
		}
		# set endpoints p1 and p2 of "y" on L2  
		$py2[$b]=$p2_lowbound+rand($p2_upbound-$p2_lowbound);  	 
	}
  
	#-- sort array 
	$px1[0]=$px2[0]=$py1[0]=$py2[0]=0; #dummy for sorting
	@px1=sort @px1; @px2=sort @px2;
	@py1=sort @py1; @py2=sort @py2;

	#--- setup L1 and L2  ---
	@L1=@L2=();@a_L1=@b_L1=@a_L2=@b_L2=();  
	#--setup L1  
	$p=$i=$j=1;
	while ( $i < scalar(@px1) && $j < scalar(@py1)){
		if ($px1[$i] < $py1[$j]){	
			$L1[$p]="x#$i"; 
			$L1x{"x$i"}=$p;
			$i++;	  	  
		}else{
			$L1[$p]="y#$j"; 
			$L1x{"y$j"}=$p;
			$j++;	  
		}
		$p++;	
	}
	while ($i < scalar(@px1)){ $L1[$p]="x#$i"; $L1x{"x$i"}=$p; $i++; $p++;}
	while ($j < scalar(@py1)){ $L1[$p]="y#$j"; $L1x{"y$j"}=$p; $j++; $p++;}
  
	#-- setup line L2  
	$p=$i=$j=1;
	while ( $i < scalar(@px2) && $j < scalar(@py2)){
		if ($px2[$i] < $py2[$j]){	       	
			$L2[$p]="x#$i"; 	  
			$L2x{"x$i"}=$p;
			$i++;	  	  
		}else{
			$L2[$p]="y#$j"; 
			$L2x{"y$j"}=$p;
			$j++;	  
		}
		$p++;	
	}
	while ($i < scalar(@px2)){ $L2[$p]="x#$i"; $L2x{"x$i"}=$p; $i++; $p++;}
	while ($j < scalar(@py2)){ $L2[$p]="y#$j"; $L2x{"y$j"}=$p; $j++; $p++;}
  
	# compute adjacent matrix
	for ($i=1; $i <= $n ; $i++){    
		for ($j=1; $j <= $m ; $j++){
			if (($L1x{"x$i"}-$L1x{"y$j"})*($L2x{"x$i"}-$L2x{"y$j"}) < 0 ){	  
				$adj[$i][$j]=1;
			} 		
		}
	}
    
	$nL1=scalar(@L1);
	$nL2=scalar(@L2);
	#------setup dummy vertices -----------------
	# add dummy vertex 'xn+1' on the rightmost side
	$L1[$nL1]="x#".($n+1);
	$L2[$nL2]="x#".($n+1);
	$L1x{"x".($n+1)}=$nL1;
	$L2x{"x".($n+1)}=$nL2;  
	# add dummy 'x0','y0' vertices on the leftmost side  
	$L1x{"x0"}=$L2x{"x0"}=0;  
	$L1x{"y0"}=$L2x{"y0"}=0;
}

sub brute_force{
	return if ($n+$m > 15);
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n+$m);
	%edge=();
	for ($a=1; $a<=$n; $a++){
		for ($b=1; $b<=$m; $b++){      
			if ($adj[$a][$b]){
				$g->add_edges([$a,$n+$b]);  #b is shifted n positions
			}
		}
	}
	
	$max=2**$g->vertices-1;
	@vc_set=();
	@vc_set = map { Set::Scalar->new() } 0..$max;

	#for checking independent perfect dominating sets
	my $all_v= Set::Scalar->new(1..$n+$m); # all vertices
	my $mis;  # maximal independet sets
	my $ipds_flag;
	my $nipds=0;

	$nvc=0;
	@min_vc_tag=();
	%hsize=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		%cover=();
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];
					$cover{$edge}=1;
				}  
				$vc_set[$num]->insert($vs);
			}
		}
		@cover_edge=keys %cover;      
		$vc=$vc_set[$num];
		if ( scalar(@cover_edge) == scalar($g->edges) ){
			$nvc++;       
			$flag=1;
			foreach $i (0..$num-1){
				if ($min_vc_tag[$i]==1){
					$mvi=$vc_set[$i];
					if ( $vc->is_proper_subset($mvi) ){
						$min_vc_tag[$i]=0;
						$flag=1;
					}elsif ( $vc->is_proper_superset($mvi) ){
						$flag=0;
						break;
					}
				}
			}
			if ($flag==1){
				$min_vc_tag[$num]=1;				
				#check independent perfect dominating sets
				$mis=$all_v-$vc; # set difference
				$ipds_flag=1;
				for my $u ($vc->elements) { # u is not in mis
					$dominated=0;
					for my $i ($mis->elements) { # i is in mis
						if ($g->has_edge($i,$u)){ # u and i are adjacent
							$dominated++; # i dominates u
						}
					}
					if ($dominated != 1){# u is dominated by more than one vertex
						$ipds_flag=0;
						break;
					}
				}
				if ($ipds_flag == 1){  # $mis is a independent perfect dominating sets
					$nipds++;
				}        
			}
		}
	}
	$nmvc=0;
	for ($i=0; $i <= $max ; $i++){
		if ($min_vc_tag[$i]==1){
			$nmvc++;
		}	
	}	
	return($nvc,$nmvc,$nipds); # note: |VC|=|IS| and |MVC|=|MIS|
}
