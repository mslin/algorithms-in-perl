#!/usr/bin/perl
#
# conut vertex covers,minimal vertex covers, minimum vertex covers, 
# and maximum minimal vertex covers in a trapezoid graph
#
# by Min-Sheng Lin
#
use Set::Scalar;  
use Graph;
$|=1;

#globals
$n=10;               # problem size
@a=@b=@c=@d=();
@top=@bottom=();
@x=();    # store x(k) 
@y=();    # stoer y(k)
@X=();    # matrix: X(i,j)=1 if Ti < Tj
@torder=(); # store topological order

while ( $test++ < 20 ){ # test 20 random instances  
  &new_g(); # create a random trapezoid graph
  print "\n== test$test: trapezoid diagram: ==\n";  
  print "@top[1..$#top]\n";  # top line
  print "@bottom[1..$#bottom]\n";  # bottom line

  print "our proposed algorithm   : ";  
  &Compute_xk();
  ($vc1)=&Compute_VC();    
  &Compute_yk();
  ($mvc1)=&Compute_MVC();    
  &Compute_sk_skx();
  ($min_mvc1,$max_mvc1)=&Compute_nsk_nskx;
  print "#vc=$vc1 #mvc=$mvc1 #min_mvc=$min_mvc1 #max_mvc=$max_mvc1\n";
  
  print "the brute-force algorithm: ";
  ($vc2,$mvc2, $min_mvc2, $max_mvc2)=&brute_force();
  print "#vc=$vc2 #mvc=$mvc2 #min_mvc=$min_mvc2 #max_mvc=$max_mvc2\n";
  
  if ( $vc1 != $vc2 || $mvc1 != $mvc2 || $min_mvc1!=$min_mvc2 || $max_mvc1!=$max_mvc2){
    print "An error occured. Stop!\n";
    exit;
  }
}                     
print "\n Tests completed successfully.\n";

sub Compute_xk {
  @x=();
  @X=();
  @x_size=();
  
  $g_t_new = Graph->new;
  for ($k=0; $k<=$n+1; $k++){
    $x[$k] = Set::Scalar->new;
    $x_size[$k]=0;
    for ($i=0; $i<=$n+1; $i++){
      if ($i!=$k && ($b[$i] < $a[$k] && $d[$i] < $c[$k])) { #implying Ti<Tk
        $x[$k]->insert($i);
        $x_size[$k]++;
        $X[$i][$k]=1;
        $g_t_new->add_edge($i,$k);
      }else {
        $X[$i][$k]=0;          # produce the relationship 0-1 matrix
      }
    }
  }     
  @torder = $g_t_new->toposort;  # produce the topological order
} 


# count vertex covers
sub Compute_VC {
  @VC=();
  $VC[0]=1;  
  for ($kk=1; $kk<=$n+1; $kk++){
    $k=$torder[$kk];
    $VC[$k]=0;  
    foreach $i ($x[$k]->elements){
      $VC[$k] = $VC[$k] + $VC[$i];
    }
  }
  return($VC[$n+1]);
}

sub Compute_yk{
  @upper_v=@rl=();
  
  for ($i=0; $i<=$n+1; $i++){
    $upper_v[$a[$i]] = $i;    
    $upper_v[$b[$i]] = $i;
	$rl[$a[$i]] = "upper_left";
    $rl[$b[$i]] = "upper_right";
  }

  @y = ();
  $y[0] = Set::Scalar->new;

  for ($k=1; $k<=$n+1; $k++){
    $y[$k] = Set::Scalar->new;
    $limit = -1;
    for ($p=$a[$k]-1; $p>=0; $p--){
      $i = $upper_v[$p];
      if ($X[$i][$k]){	    
        if ($rl[$p] eq "upper_right" && $d[$i] > $limit){
          $y[$k] = $y[$k] + $i;
		}  
        if ($rl[$p] eq "upper_left"){
		  $limit = ($limit > $c[$i])? $limit : $c[$i];
		}     
      }  
	}
  }
}

# count minimal vertex covers
sub Compute_MVC {
  @MVC=();
  $MVC[0]=1;  
  for ($kk=1; $kk<=$n+1; $kk++){
    $k=$torder[$kk];
    $MVC[$k]=0;      
    foreach $i ($y[$k]->elements){
      $MVC[$k] = $MVC[$k] + $MVC[$i];
    }
  }#for kk
  return($MVC[$n+1]);
}

# compute s(k) and s*(k), the minimum size of VCs and the maximum size of minimal VCs, respectively
sub Compute_sk_skx {
  @s=@sx=();
  $s[0]=0;  $sx[0]=0;
  for ($kk=1; $kk<=$n+1; $kk++){
    $k=$torder[$kk];   
	$s[$k]=$n+1; $sx[$k]=-1;
    foreach $i ($y[$k]->elements){
      if ( $s[$i]+$x_size[$k]-$x_size[$i]-1 < $s[$k] ){
         $s[$k]=$s[$i]+$x_size[$k]-$x_size[$i]-1;
	  }	 
	  if ( $sx[$i]+$x_size[$k]-$x_size[$i]-1 > $sx[$k] ){
         $sx[$k]=$sx[$i]+$x_size[$k]-$x_size[$i]-1;
	  }	 
    }
  }
}

# compute #s(k) and #s*(k), the number minimal vertex covers with the minimum size and maximum size, respectively
sub Compute_nsk_nskx {
  @ns=@nsx=();
  $ns[0]=$nsx[0]=1;  
  for ($kk=1; $kk<=$n+1; $kk++){
    $k=$torder[$kk];    
	$ns[$k]=$nsx[$k]=0;
    foreach $i ($y[$k]->elements){      
      $ns[$k]+= $ns[$i] if ($s[$i]+$x_size[$k]-$x_size[$i]-1 == $s[$k]);
	  $nsx[$k]+= $nsx[$i] if ($sx[$i]+$x_size[$k]-$x_size[$i]-1 == $sx[$k]);
    }
  }#for kk
  return($ns[$n+1],$nsx[$n+1]);
}

sub new_g{
  @a=@b=@c=@d=();
  @top=@bottom=();
  %p1=%p2=();
  for ($v=1; $v <=$n ; $v++){
    # top line
    $p1{"$v#a"}=rand(1);
	$p1{"$v#b"}=rand(1);
	if ($p1{"$v#a"} > $p1{"$v#b"}){ #swap
	  $tmp=$p1{"$v#b"};
	  $p1{"$v#b"}=$p1{"$v#a"};
	  $p1{"$v#a"}=$tmp;
	}
	# bottom line
    $p2{"$v#c"}=rand(1);
	$p2{"$v#d"}=rand(1);
	if ($p2{"$v#c"} > $p2{"$v#d"}){ #swap
	  $tmp=$p2{"$v#d"};
	  $p2{"$v#d"}=$p2{"$v#c"};
	  $p2{"$v#c"}=$tmp;
	}	
  }
  
  @key1 = sort {$p1{$a}<=>$p1{$b}} keys(%p1); #sort by p values from right to left    
  $pi=0;
  foreach $k (@key1){  # re-arrange the positions of endpoints ai and bi for all vi    
    $pi++;
	($v, $ab)=split("#",$k); 	
	$top[$pi]=$v;    
    $ab eq "a" ? $a[$v]=$pi : $b[$v]=$pi;	
  }    
  
  @key2 = sort {$p2{$a}<=>$p2{$b}} keys(%p2); #sort by p values from right to left    
  $pi=0;
  foreach $k (@key2){  # re-arrange the positions of endpoints ci and di for all vi    
    $pi++;
	($v, $cd)=split("#",$k); 	
	$bottom[$pi]=$v;    
    $cd eq "c" ? $c[$v]=$pi : $d[$v]=$pi;	
  }    

  # Add two dummy vertices 
  $a[$n+1]=$b[$n+1]=$c[$n+1]=$d[$n+1]=2*$n+1;
  $a[0]=$b[0]=$c[0]=$d[0]=0;  
}


sub brute_force {  
  $g = Graph::Undirected->new();
  $g->add_vertices(1..$n);
  for ($v=1; $v <= $n-1 ; $v++){
    for ($u=$v+1 ; $u <= $n ; $u++){
	  if (!(($b[$v]<$a[$u] && $d[$v]<$c[$u]) || ($b[$u]<$a[$v] && $d[$u]<$c[$v]))){
	    $g->add_edges([$v,$u]);
	  }	
	}
  }	
  
  $max=2**$g->vertices-1;
  @v_set = map { Set::Scalar->new() } 0..$max;
  $vc=0;  
  @min_vc_tag=();
  foreach $num (0..$max){
    $bits = unpack ( "B*", pack("N",$num) );    
    @bit =reverse(split(//,$bits));     	
    %cover=();
    foreach $v ($g->vertices){
      if ($bit[$v-1] == 1){ # select vertex v
	    $v_set[$num]->insert($v);		        
        foreach $e ($g->edges_at($v)){
          $edge=$$e[0].'-'.$$e[1];
          $cover{$edge}=1;  # v covers edge e
        }          
      }
    } #foreach v
    	    
    if ( scalar(keys %cover) == scalar($g->edges) ){ # $v_set[$num] is a vertex cover
      $vc++; 
	  # check if $v_set[$num] is a minimal vertex cover
      $min_vc_tag[$num]=1;	                 
      foreach $i (0..$num-1){
        if ($min_vc_tag[$i]==1){          
          if ( $v_set[$num]->is_proper_subset($v_set[$i]) ){
            $min_vc_tag[$i]=0; # $v_set[$i] is not a minimal vertex cover            
          }elsif ( $v_set[$num]->is_proper_superset($v_set[$i]) ){
            $min_vc_tag[$num]=0; # $v_set[$num] is not a minimal vertex cover            
            break;
          }
        }
      }
    }
  }

  $mvc=0;  
  %hsize=();  
  for ($i=0; $i <= $max ; $i++){
    if ($min_vc_tag[$i]==1){
      $mvc++;	  
      $hsize{$v_set[$i]->size}++;
    }
  }  
  @size= (sort {$a<=>$b} keys %hsize);  
  return($vc, $mvc, $hsize{$size[0]}, $hsize{$size[$#size]});
}
