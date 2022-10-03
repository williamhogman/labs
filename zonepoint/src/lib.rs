use geo::algorithm::bounding_rect::BoundingRect;
use geo::algorithm::euclidean_distance::EuclideanDistance;
use geo::intersects::Intersects;
use geo::polygon;
use geo::CoordNum;
use geo::MultiPolygon;
use geo::Point;
use geo::Polygon;
use rstar::{PointDistance, RTree, RTreeObject, AABB};

struct Zone<T: CoordNum> {
    geometry: MultiPolygon<T>,
}

impl<T: CoordNum> Zone<T> {
    fn new(geometry: MultiPolygon<T>) -> Zone<T> {
        Zone { geometry }
    }
}

fn aaab_from_rect(r: geo::Rect<f64>) -> AABB<[f64; 2]> {
    let ((min_x, min_y), (max_x, max_y)) = (r.min().x_y(), r.max().x_y());
    AABB::from_corners([min_x, min_y], [max_x, max_y])
}

impl RTreeObject for Zone<f64> {
    type Envelope = AABB<[f64; 2]>;
    fn envelope(&self) -> Self::Envelope {
        aaab_from_rect(self.geometry.bounding_rect().unwrap())
    }
}

impl PointDistance for Zone<f64> {
    fn distance_2(&self, point: &[f64; 2]) -> f64 {
        let point = geo::Point::new(point[0], point[1]);
        self.geometry.euclidean_distance(&point)
    }
    fn contains_point(&self, point: &[f64; 2]) -> bool {
        let point: Point<f64> = Point::new(point[0], point[1]);
        self.geometry.intersects(&point)
    }
}

struct ZoneMap {
    tree: RTree<Zone<f64>>,
}

impl ZoneMap {
    fn new() -> Self {
        ZoneMap { tree: RTree::new() }
    }

    fn insert(&mut self, zone: Zone<f64>) {
        self.tree.insert(zone);
    }

    fn zones_for_point(&self, point: (f64, f64)) -> Vec<&Zone<f64>> {
        self.tree.locate_all_at_point(&[point.0, point.1]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        let a_el: Polygon<f64> =
            polygon![(x: 0., y: 0.), (x: 5., y: 0.), (x: 7., y: 9.), (x: 0., y: 0.)];
        let a = MultiPolygon::new(vec![a_el]);
        let z = Zone::<f64>::new(a);
        let mut zm: ZoneMap = ZoneMap::new();
        zm.insert(z);
        let point = (2., 2.);
        let zones = zm.zones_for_point(point.into());
        assert_eq!(zones.len(), 1);
        let p2 = (100., 100.);
        let zones = zm.zones_for_point(p2.into());
        assert_eq!(zones.len(), 0);
    }
}
